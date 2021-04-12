#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

int main()
{
    printf("BEGIN\n");

    int dirfd, fd1, fd2, fd3;

    dirfd = open("src", O_DIRECTORY);
    printf("open src -> %d\n", dirfd);

    fd1 = open("src/mount.c", O_RDWR);
    printf("open src/mount.c -> %d\n", fd1);

    fd2 = open("src/mq.c", O_RDWR);
    printf("open src/mq.c -> %d\n", fd2);

    printf("END\n");
    return 0;
}
