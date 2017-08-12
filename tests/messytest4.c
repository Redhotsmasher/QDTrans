#include <pthread.h>
#include <semaphore.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

typedef struct{
    pthread_mutex_t lock;
    short value;
    char* stuff;
}SharedInt;

sem_t sem;
SharedInt* sip;

void *functionWithCriticalSection(short v) {
    // Do some work
    pthread_mutex_lock(&(sip->lock));
    printf("Crit %i executed by %u.\n", 1, getpid());
    sip->value = sip->value + v;
    pthread_mutex_unlock(&(sip->lock));
    // Do some more work
    sem_post(&sem);
}

void *function2WithCriticalSection(int* v2) {
    // Do some work
    int pul = 1337;
    char* ollon = NULL;
    short v3 = *v2;
    pthread_mutex_lock(&(sip->lock));
    printf("Crit %i executed by %u.\n", 2, getpid());
    for (int i = 0; i < v3; i++) {
        strcat(sip->stuff, " ");
    }
    pthread_mutex_unlock(&(sip->lock));
    // Do some more work
    sem_post(&sem);
}

int main() {
    int limit = 16;
    sem_init(&sem, 0, 0);
    SharedInt si;
    si.stuff = malloc(80000*sizeof(char));
    sip = &si;
    sip->value = 0;
    int v2 = 1;
    pthread_mutex_init(&(sip->lock), NULL);
    for(int i = 0; i < limit; i++) {
        pthread_t thread1;
        pthread_t thread2;
        pthread_create (&thread1,NULL,functionWithCriticalSection,v2);
        pthread_create (&thread2,NULL,function2WithCriticalSection,&v2);
    }
    for(int i = 0; i < 2*limit; i++) {
        sem_wait(&sem);
    }
    pthread_mutex_destroy(&(sip->lock));
    sem_destroy(&sem);
    int stringlength = strlen(si.stuff);
    free(si.stuff);
    printf("%d\n", sip->value-stringlength); // Should print "0".
    return sip->value-stringlength;
}
