#ifndef PRINTING_H
#define PRINTING_H

#include <stdbool.h>

#define RELATIVE_POINTERS true

/* Define printFormatter to be a function pointer type taking a sinle parameter
 * (a header pointer) and returning void
 *
 * This allows the print freelist and tags functions to take various printing
 * functions depending on the kind of output desired
 *
 * https://www.cprogramming.com/tutorial/function-pointers.html
 */
typedef void (*printFormatter)(header *);

/* Functions defining a format to print */
void basic_print(header * block);
void print_list(header * block);
void print_object(header * block);
void print_status(header * block);

/* Functions to print the freelist structure taking a
 * one of the above printing functions as a function pointer
 */
void freelist_print(printFormatter pf);

// void chunklist_print(printFormatter pf);
/* Helpers */
void print_pointer(void * p);

#endif // PRINTING_H
