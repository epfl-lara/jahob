#include <mlvalues.h>
#include <unistd.h>

CAMLprim value unix_fork_with_pgid(value unit)
{
  int ret;
  ret = fork();
  setpgid(ret, 0);
  // if (ret == -1) uerror("fork", Nothing);
  return Val_int(ret);
}
