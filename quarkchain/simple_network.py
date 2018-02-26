
import asyncio
import argparse
import ipaddress
import socket
from quarkchain.core import Transaction, MinorBlockHeader, MinorBlock
from quarkchain.core import RootBlock, RootBlockHeader
from quarkchain.core import Serializable, PreprendedSizeListSerializer, PreprendedSizeBytesSerializer
from quarkchain.core import uint16, uint32, uint128, hash256
from quarkchain.core import random_bytes
from quarkchain.config import DEFAULT_ENV
from quarkchain.chain import QuarkChainState
from quarkchain.protocol import Connection, ConnectionState
from quarkchain.local import LocalServer
from quarkchain.db import PersistentDb

SEED_HOST = ("localhost", 38291)


class HelloCommand(Serializable):
    FIELDS = [
        ("version", uint32),
        ("networkId", uint32),
        ("peerId", hash256),
        ("peerIp", uint128),
        ("peerPort", uint16),
        ("shardMaskList", PreprendedSizeListSerializer(
            4, uint32)),  # TODO create shard mask object
        ("rootBlockHeader", RootBlockHeader)
    ]

    def __init__(self,
                 version=0,
                 networkId=0,
                 peerId=bytes(32),
                 peerIp=int(ipaddress.ip_address("127.0.0.1")),
                 peerPort=38291,
                 shardMaskList=None,
                 rootBlockHeader=None):
        shardMaskList = shardMaskList if shardMaskList is not None else []
        rootBlockHeader = rootBlockHeader if rootBlockHeader is not None else []
        fields = {k: v for k, v in locals().items() if k != 'self'}
        super(type(self), self).__init__(**fields)


class NewMinorBlockHeaderListCommand(Serializable):
    FIELDS = [
        ("rootBlockHeader", RootBlockHeader),
        ("minorBlockHeaderList", PreprendedSizeListSerializer(4, MinorBlockHeader)),
    ]

    def __init__(self, rootBlockHeader, minorBlockHeaderList):
        self.rootBlockHeader = rootBlockHeader
        self.minorBlockHeaderList = minorBlockHeaderList


class NewTransactionListCommand(Serializable):
    FIELDS = [
        ("transactionList", PreprendedSizeListSerializer(4, Transaction))
    ]

    def __init__(self, transactionList=None):
        self.transactionList = transactionList if transactionList is not None else []


class GetRootBlockListRequest(Serializable):
    FIELDS = [
        ("rootBlockHashList", PreprendedSizeListSerializer(4, hash256))
    ]

    def __init__(self, rootBlockHashList=None):
        self.rootBlockHashList = rootBlockHashList if rootBlockHashList is not None else []


class GetRootBlockListResponse(Serializable):
    FIELDS = [
        ("rootBlockList", PreprendedSizeListSerializer(4, RootBlock))
    ]

    def __init__(self, rootBlockList=None):
        self.rootBlockList = rootBlockList if rootBlockList is not None else []


class GetMinorBlockListRequest(Serializable):
    FIELDS = [
        ("minorBlockHashList", PreprendedSizeListSerializer(4, hash256))
    ]

    def __init__(self, minorBlockHashList=None):
        self.minorBlockHashList = minorBlockHashList if minorBlockHashList is not None else []


class GetMinorBlockListResponse(Serializable):
    FIELDS = [
        ("minorBlockList", PreprendedSizeListSerializer(4, MinorBlock))
    ]

    def __init__(self, minorBlockList=None):
        self.minorBlockList = minorBlockList if minorBlockList is not None else []


class GetBlockHeaderListRequest(Serializable):
    FIELDS = [
        ("blockHash", hash256),
        ("maxBlocks", uint32),
        ("direction", uint8),       # 0 to genesis, 1 to tip
    ]

    def __init__(self, blockHash, maxBlocks, direction):
        self.blockHash = blockHash
        self.maxBlocks = maxBlocks
        self.direction = direction


class GetBlockHeaderListResponse(Serializable):
    FIELDS = [
        ("isRoot", uint8),
        ("blockHeaderList", PreprendedSizeListSerializer(4, PreprendedSizeBytesSerializer))
    ]

    def __init__(self, isRoot, blockHeaderList):
        self.isRoot = isRoot
        self.blockHeaderList = blockHeaderList


class GetPeerListRequest(Serializable):
    FIELDS = [
        ("maxPeers", uint32),
    ]

    def __init__(self, maxPeers):
        self.maxPeers = maxPeers


class PeerInfo(Serializable):
    FIELDS = [
        ("ip", uint128),
        ("port", uint16),
    ]

    def __init__(self, ip, port):
        self.ip = ip
        self.port = port


class GetPeerListResponse(Serializable):
    FIELDS = [
        ("peerInfoList", PreprendedSizeListSerializer(4, PeerInfo))
    ]

    def __init__(self, peerInfoList=None):
        self.peerInfoList = peerInfoList if peerInfoList is not None else []


class CommandOp():
    HELLO = 0
    NEW_MINOR_BLOCK_HEADER_LIST = 1
    NEW_TRANSACTION_LIST = 2
    GET_ROOT_BLOCK_LIST_REQUEST = 3
    GET_ROOT_BLOCK_LIST_RESPONSE = 4
    GET_PEER_LIST_REQUEST = 5
    GET_PEER_LIST_RESPONSE = 6
    GET_MINOR_BLOCK_LIST_REQUEST = 7
    GET_MINOR_BLOCK_LIST_RESPONSE = 8
    GET_BLOCK_HEADER_LIST_REQUEST = 9
    GET_BLOCK_HEADER_LIST_RESPONSE = 10


OP_SERIALIZER_MAP = {
    CommandOp.HELLO: HelloCommand,
    CommandOp.NEW_MINOR_BLOCK_HEADER_LIST: NewMinorBlockHeaderListCommand,
    CommandOp.NEW_TRANSACTION_LIST: NewTransactionListCommand,
    CommandOp.GET_ROOT_BLOCK_LIST_REQUEST: GetRootBlockListRequest,
    CommandOp.GET_ROOT_BLOCK_LIST_RESPONSE: GetRootBlockListResponse,
    CommandOp.GET_PEER_LIST_REQUEST: GetPeerListRequest,
    CommandOp.GET_PEER_LIST_RESPONSE: GetPeerListResponse,
    CommandOp.GET_MINOR_BLOCK_LIST_REQUEST: GetMinorBlockListRequest,
    CommandOp.GET_MINOR_BLOCK_LIST_RESPONSE: GetMinorBlockListResponse,
    CommandOp.GET_BLOCK_HEADER_LIST_REQUEST: GetBlockHeaderListRequest,
    CommandOp.GET_BLOCK_HEADER_LIST_RESPONSE: GetBlockHeaderListResponse,
}


class Peer(Connection):

    def __init__(self, env, reader, writer, network):
        super().__init__(env, reader, writer, OP_SERIALIZER_MAP, OP_NONRPC_MAP, OP_RPC_MAP)
        self.network = network

        # The following fields should be set once active
        self.id = None
        self.shardMaskList = None
        self.bestRootBlockHeaderObserved = None

    def sendHello(self):
        cmd = HelloCommand(version=self.env.config.P2P_PROTOCOL_VERSION,
                           networkId=self.env.config.NETWORK_ID,
                           peerId=self.network.selfId,
                           peerIp=int(self.network.ip),
                           peerPort=self.network.port,
                           shardMaskList=[],
                           rootBlockHeader=RootBlockHeader())
        # Send hello request
        self.writeCommand(CommandOp.HELLO, cmd)

    async def start(self, isServer=False):
        op, cmd, rpcId = await self.readCommand()
        if op is None:
            assert(self.state == ConnectionState.CLOSED)
            return "Failed to read command"

        if op != CommandOp.HELLO:
            return self.closeWithError("Hello must be the first command")

        if cmd.version != self.env.config.P2P_PROTOCOL_VERSION:
            return self.closeWithError("incompatible protocol version")

        if cmd.networkId != self.env.config.NETWORK_ID:
            return self.closeWithError("incompatible network id")

        self.id = cmd.peerId
        self.shardMaskList = cmd.shardMaskList
        self.ip = ipaddress.ip_address(cmd.peerIp)
        self.port = cmd.peerPort
        self.bestRootBlockHeaderObserved = cmd.rootBlockHeader
        # TODO handle root block header
        if self.id == self.network.selfId:
            # connect to itself, stop it
            return self.closeWithError("Cannot connect to itself")

        if self.id in self.network.activePeerPool:
            return self.closeWithError("Peer %s already connected" % self.id)

        self.network.activePeerPool[self.id] = self
        print("Peer {} connected".format(self.id.hex()))

        # Send hello back
        if isServer:
            self.sendHello()

        asyncio.ensure_future(self.activeAndLoopForever())
        return None

    def close(self):
        if self.state == ConnectionState.ACTIVE:
            assert(self.id is not None)
            if self.id in self.network.activePeerPool:
                del self.network.activePeerPool[self.id]
            print("Peer {} disconnected, remaining {}".format(
                self.id.hex(), len(self.network.activePeerPool)))
        super().close()

    def closeWithError(self, error):
        print("Closing peer %s with the following reason: %s" %
              (self.id.hex() if self.id is not None else "unknown", error))
        return super().closeWithError(error)

    async def handleError(self, op, cmd, rpcId):
        self.closeWithError("Unexpected op {}".format(op))

    async def handleNewMinorBlockHeaderList(self, op, cmd, rpcId):
        # Make sure the root block heigh is non-decreasing
        rHeader = cmd.rootBlockHeader
        if self.bestRootBlockHeaderObserved.height > rHeader.height:
            self.closeWithError("Root block height should be non-decreasing")
            return
        elif self.bestRootBlockHeaderObserved.height == rHeader.height:
            if self.bestRootBlockHeaderObserved != cmd.rootBlockHeader:
                self.closeWithError(
                    "Root block the same height should not be changed")
                return
        elif rHeader.shardInfo.getShardSize() != self.bestRootBlockHeaderObserved.shardInfo.getShardSize():
            # TODO: Support reshard
            self.closeWithError("Incorrect root block shard size")
            return
        else:
            self.bestRootBlockHeaderObserved = rHeader

        # if self.bestRootBlockHeaderObserved.height == rHeader.height:
        #     # Check if any new minor blocks mined
        #     downloadList = []
        #     for mHeader in cmd.minorBlockHeaderList:
        #         if mHeader.branch.getShardSize() != rHeader.shardInfo.getShardSize():
        #             self.closeWithError("Incorrect minor block shard size")
        #             return
                # if mHeader.height < self.network.qcState.

    async def handleGetRootBlockListRequest(self, request):
        return GetRootBlockListResponse()

    async def handleGetBlockHeaderListRequest(self, request):
        

    async def handleGetPeerListRequest(self, request):
        resp = GetPeerListResponse()
        for peerId, peer in self.network.activePeerPool.items():
            if peer == self:
                continue
            resp.peerInfoList.append(PeerInfo(int(peer.ip), peer.port))
            if len(resp.peerInfoList) >= request.maxPeers:
                break
        return resp


# Only for non-RPC (fire-and-forget) and RPC request commands
OP_NONRPC_MAP = {
    CommandOp.HELLO: Peer.handleError,
}

# For RPC request commands
OP_RPC_MAP = {
    CommandOp.GET_ROOT_BLOCK_LIST_REQUEST:
        (CommandOp.GET_ROOT_BLOCK_LIST_RESPONSE,
         Peer.handleGetRootBlockListRequest),
    CommandOp.GET_PEER_LIST_REQUEST:
        (CommandOp.GET_PEER_LIST_RESPONSE, Peer.handleGetPeerListRequest)
    CommandOp.GET_BLOCK_HEADER_LIST_REQUEST:
        (CommandOp.GET_BLOCK_HEADER_LIST_RESPONSE, Peer.handleGetBlockHeaderListRequest)
}


class SimpleNetwork:

    def __init__(self, env, qcState):
        self.loop = asyncio.get_event_loop()
        self.env = env
        self.activePeerPool = dict()    # peer id => peer
        self.selfId = random_bytes(32)
        self.qcState = qcState
        self.ip = ipaddress.ip_address(
            socket.gethostbyname(socket.gethostname()))
        self.port = self.env.config.P2P_SERVER_PORT
        self.localPort = self.env.config.LOCAL_SERVER_PORT

    async def newClient(self, client_reader, client_writer):
        peer = Peer(self.env, client_reader, client_writer, self)
        await peer.start(isServer=True)

    async def newLocalClient(self, reader, writer):
        localServer = LocalServer(self.env, reader, writer, self)
        await localServer.start()

    async def connect(self, ip, port):
        print("connecting {} {}".format(ip, port))
        try:
            reader, writer = await asyncio.open_connection(ip, port, loop=self.loop)
        except Exception as e:
            print("failed to connect {} {}: {}".format(ip, port, e))
            return None
        peer = Peer(self.env, reader, writer, self)
        peer.sendHello()
        result = await peer.start(isServer=False)
        if result is not None:
            return None
        return peer

    async def connectSeed(self, ip, port):
        peer = await self.connect(ip, port)
        if peer is None:
            # Fail to connect
            return

        try:
            op, resp, rpcId = await peer.writeRpcRequest(
                CommandOp.GET_PEER_LIST_REQUEST, GetPeerListRequest(10))
        except Exception as e:
            return

        print("connecting {} peers ...".format(len(resp.peerInfoList)))
        for peerInfo in resp.peerInfoList:
            asyncio.ensure_future(self.connect(
                str(ipaddress.ip_address(peerInfo.ip)), peerInfo.port))

    def shutdownPeers(self):
        activePeerPool = self.activePeerPool
        self.activePeerPool = dict()
        for peerId, peer in activePeerPool.items():
            peer.close()

    def start(self):
        coro = asyncio.start_server(
            self.newClient, "0.0.0.0", self.port, loop=self.loop)
        self.server = self.loop.run_until_complete(coro)
        print("Self id {}".format(self.selfId.hex()))
        print("Listening on {} for p2p".format(
            self.server.sockets[0].getsockname()))

        if self.env.config.LOCAL_SERVER_ENABLE:
            coro = asyncio.start_server(
                self.newLocalClient, "127.0.0.1", self.localPort, loop=self.loop)
            self.local_server = self.loop.run_until_complete(coro)
            print("Listening on {} for local".format(
                self.local_server.sockets[0].getsockname()))

        self.loop.create_task(self.connectSeed(SEED_HOST[0], SEED_HOST[1]))

        try:
            self.loop.run_forever()
        except KeyboardInterrupt:
            pass

        self.shutdownPeers()
        self.server.close()
        self.loop.run_until_complete(self.server.wait_closed())
        self.loop.close()
        print("Server is shutdown")


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--server_port", default=DEFAULT_ENV.config.P2P_SERVER_PORT, type=int)
    # Local port for JSON-RPC, wallet, etc
    parser.add_argument(
        "--enable_local_server", default=False, type=bool)
    parser.add_argument(
        "--local_port", default=DEFAULT_ENV.config.LOCAL_SERVER_PORT, type=int)
    parser.add_argument("--in_memory_db", default=False)
    args = parser.parse_args()

    env = DEFAULT_ENV.copy()
    env.config.P2P_SERVER_PORT = args.server_port
    env.config.LOCAL_SERVER_PORT = args.local_port
    env.config.LOCAL_SERVER_ENABLE = args.enable_local_server
    if not args.in_memory_db:
        env.db = PersistentDb(path="./db", clean=True)

    return env


def main():
    env = parse_args()
    env.NETWORK_ID = 1  # testnet

    qcState = QuarkChainState(env)
    network = SimpleNetwork(env, qcState)
    network.start()


if __name__ == '__main__':
    main()
