#include <stdlib.h>
#include <stdio.h>
#include <pthread.h>

pthread_mutex_t lock;

int main() {

    pthread_mutex_init(&lock, NULL);
    pthread_mutex_lock(&lock);
    printf("Line 1\n");
    1+1;
    printf("Line 3\n");
    pthread_mutex_unlock(&lock);
    printf("Line inbetween critical sections\n");
    pthread_mutex_lock(&lock);
    printf("Line 4\n");
    int twoplustwo;
    twoplustwo = 2+2;
    printf("Line 6\n");
    pthread_mutex_unlock(&lock);
    pthread_mutex_destroy(&lock);
    
}
