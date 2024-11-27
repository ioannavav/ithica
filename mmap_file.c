#define _GNU_SOURCE
#include <sys/types.h>
#include <sys/mman.h>
#include <err.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sched.h>
#include <time.h>

#define MAX_BUFFER_SIZE 1024


void print_cpu_id() {
	int cpu = sched_getcpu();
	printf("Running on CPU: %d\n", cpu);
}

struct ExecutionInfo {
	unsigned int timesFailed;
};

struct ExecutionInfo * dump;
int fd = -1;
int error_count = 0;
int print_enabled = 1;

int setup(unsigned int size) {
	if ((fd = open("llvmdump", O_RDWR, 0)) == -1)
		err(1, "can't open");

	dump = (struct ExecutionInfo *) mmap(NULL, 1048576, PROT_READ|PROT_WRITE, MAP_SHARED, fd, 0);

	if (dump == MAP_FAILED) 
		errx(1, "map failed");

  memset(dump, 0, 1048576);

	return 1;
}

int incr_err(unsigned int block, unsigned int total) {
	if (fd == -1) {
		setup(total);
	}

	dump[block].timesFailed++;

  error_count++;

  // Stop printing after limit.
  if (error_count > 1000) {
		print_enabled = 0;
    printf("Stopping printing by design......");
	}	

	return error_count;
}


void conditional_print(const char* message) {
		if (print_enabled) {
				fprintf(stderr, "%s\n", message);
		}
}

void fprintFunc(const char* message, ...) {
	va_list argptr;
	va_start(argptr, message);
	vfprintf(stderr, message, argptr);
	va_end(argptr);
}


void print_date(const char* libraryName) {
    time_t rawtime;
    struct tm * timeinfo;
    char buffer[80];

    // Get the current date and time
    time(&rawtime);
    timeinfo = localtime(&rawtime);

    // Format the time into a readable string
    strftime(buffer, sizeof(buffer), "%Y-%m-%d %H:%M:%S", timeinfo);
    
    // Print the formatted date and time, and library name
    printf("Library: %s | Current Date and Time: %s\n", libraryName, buffer);
}


int * printMemoryAsHex(volatile const unsigned char * buff1, int sizeInBytes1, volatile const unsigned char * buff2, int sizeInBytes2) {
    char originalValue[MAX_BUFFER_SIZE * 3 + 1];
    char duplicateValue[MAX_BUFFER_SIZE * 3 + 1];

    if (sizeInBytes1 > MAX_BUFFER_SIZE || sizeInBytes2 > MAX_BUFFER_SIZE) {
        fprintf(stderr, "Buffer size exceeds the maximum limit\n");
        return NULL;
    }

    for (int i = 0; i < sizeInBytes1; ++i) {
        sprintf(&originalValue[i * 3], "%02x ", buff1[i]);
    }
    originalValue[sizeInBytes1 * 3] = '\0'; // Null-terminate the string

    for (int i = 0; i < sizeInBytes2; ++i) {
        sprintf(&duplicateValue[i * 3], "%02x ", buff2[i]);
    }
    duplicateValue[sizeInBytes2 * 3] = '\0'; 

    if (strcmp(originalValue, duplicateValue) != 0) {
				fprintf(stderr, "THIS ONE IS DIFFERENT:\n");
    }
    fprintf(stderr, "Original value:  %s\n", originalValue);
    fprintf(stderr, "Duplicate value: %s\n", duplicateValue);

    return 0;
}

