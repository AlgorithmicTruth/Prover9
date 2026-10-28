/* Check that zap_flatterm() does not read a flatterm after freeing it.

   free_mem() keeps small blocks on its own avail lists, so a freed
   flatterm keeps its contents and a stale read of it goes unnoticed,
   even by valgrind or ASan.  Linked with -Wl,--wrap=free_mem, every
   free_mem() call from another object file comes here first, and the
   block is filled with a byte pattern that is not a valid address, so
   following a pointer out of a freed block crashes instead.

   Build and run by test.src/memory_safety_test.sh ('make test11'). */

#include <string.h>
#include "../ladr/top_input.h"
#include "../ladr/flatterm.h"

void __real_free_mem(void *q, unsigned n);
void __wrap_free_mem(void *q, unsigned n);

void __wrap_free_mem(void *q, unsigned n)
{
  if (q != NULL && n > 1)
    memset((void **) q + 1, 0xde, (n - 1) * sizeof(void *));
  __real_free_mem(q, n);
}  /* __wrap_free_mem */

int main(void)
{
  Term t;
  Flatterm f;

  init_standard_ladr();
  t = parse_term_from_string("f(g(x,a),b)");
  f = term_to_flatterm(t);
  zap_flatterm(f);
  zap_term(t);
  printf("zap_flatterm ok\n");
  return 0;
}  /* main */
