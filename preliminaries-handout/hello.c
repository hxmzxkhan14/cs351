#include <stdio.h>

#include "hello.h"

void
say_hello_to (const char* target)
{
  printf("Hello %s!\n", target);
}

void
author (void)
{
  printf("Hello %s, %s, %s\n", name, email_username, aid);
}
