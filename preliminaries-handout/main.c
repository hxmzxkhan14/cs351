// Code for the Preliminary lab in CS351
// Nik Sultana, Illinois Tech, August 2022
#include <string.h>
#include <stdio.h>
#include "hello.h"

const char *name = "Mohammed Azhar Khan"; // TODO replace NAME with your name.
const char *email_username = "mkhan114"; // TODO replace EMAIL with your @hawk.iit.edu username, but without the "@hawk.iit.edu" part.
const char *aid = "A20493536"; // TODO replace AID with your IIT A# number.

int
main (int argc, const char *argv[])
{
  if (1 == argc) {
    say_hello_to("world");
  } else if (0 == strcmp("me", argv[1])) {
    say_hello_to (name);
  /* } if .. TODO insert additional behaviour here:
                  - if the command-line parameter is "author" then call the author() function.
                  - otherwise simply call say_hello_to() but passing it the command-line parameter.
  */
  } else if (0 == strcmp("author", argv[1])) {
    author();
  } else {
    int i;
    for (i = 1; i < argc; i++) {
    say_hello_to(argv[i]);
    }
  }
  return 0;
}
