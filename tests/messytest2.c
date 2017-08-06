#include <pthread.h>
#include <semaphore.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct{
    pthread_mutex_t lock;
    int value;
}SharedInt;

sem_t sem;
SharedInt* sip;

void *functionWithCriticalSection(int* v2) {
    // Do some work
    pthread_mutex_lock(&(sip->lock));
    sip->value = sip->value + *v2;
    int currvalue = sip->value;
    pthread_mutex_unlock(&(sip->lock));
    printf("Current value was %i.\n", currvalue);
    // Do some more work
    sem_post(&sem);
}

int main() {
    sem_init(&sem, 0, 0);
    SharedInt si;
    sip = &si;
    sip->value = 0;
    int v2 = 1;
    pthread_mutex_init(&(sip->lock), NULL);
    pthread_t thread1;
    pthread_t thread2;
    pthread_create (&thread1,NULL,functionWithCriticalSection,&v2);
    pthread_create (&thread2,NULL,functionWithCriticalSection,&v2);
    sem_wait(&sem);
    sem_wait(&sem);
    pthread_mutex_destroy(&(sip->lock));
    sem_destroy(&sem);
    printf("%d\n", sip->value); // Should print "2".
    return sip->value-2;
}
                                                                                                                                                                                                                                                                                                                                                                                                                
                                                                                                                                                                                                                                                                                                                                                                                                                
                                                                                                                                                                                                                                                                                                                                                                                                                
