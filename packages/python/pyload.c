
#include "py4yap.h"


X_API bool init_python_dll(void);


X_API bool init_python_dll(void)
{
    do_init_python();

  return 1;
}
#ifdef _WIN32

#include <windows.h>

int WINAPI win_python(HANDLE, DWORD, LPVOID);

int WINAPI win_python(HANDLE hinst, DWORD reason, LPVOID reserved) {
    switch (reason) {
        case DLL_PROCESS_ATTACH:
            break;
        case DLL_PROCESS_DETACH:
            break;
        case DLL_THREAD_ATTACH:
            break;
        case DLL_THREAD_DETACH:
            break;
    }
    return 1;
}
#endif
