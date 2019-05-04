CC=g++
CFLAGS=-Wall -O3 -std=c++17

all: qkchash libqkchash.so qkchash-cu

qkchash: qkchash.cpp
	$(CC) $(CFLAGS) -o qkchash qkchash.cpp

libqkchash.so: qkchash.cu
	#$(CC) $(CFLAGS) -o libqkchash.so -shared -fPIC qkchash.cpp
	nvcc -I. -arch sm_60 --compiler-options '-fPIC' -dc qkchash.cu -o qkchash_kernel.o
	nvcc -arch sm_60 --compiler-options '-fPIC' -dlink qkchash_kernel.o -o qkchash_cu.o
	g++ -shared -o libqkchash.so qkchash_kernel.o qkchash_cu.o -lcudart

qkchash-cu: qkchash.cu
	#nvcc -arch=sm_60 -I. -o qkchash-cu qkchash.cu --ptxas-options=-v -g -G -rdc=true
	EXTRA_NVCCFLAGS="-L /usr/lib/x86_64-linux-gnu" nvcc -arch=sm_60 -I. -o qkchash-cu qkchash.cu --ptxas-options=-v -rdc=true

clean:
	rm -f qkchash libqkchash.so
