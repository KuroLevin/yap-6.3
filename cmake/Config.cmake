remove_definitions(























































































)

# modern systems do this.

set(MALLOC_T "void *")
OPTION(WITH_SYSTEM_MALLOC
        "use malloc to allocate memory" ON)
OPTION(WITH_DL_MALLOC
        "use malloc to allocate memory" OFF)
OPTION(WITH_YAP_MALLOC
        "use malloc to allocate mem
        ory" OFF)

if (WITH_SYSTEM_MALLOC)
    set_property(DIRECTORY APPEND PROPERTY COMPILE_DEFINITIONS USE_SYSTEM_MALLOC=1)
elseif (WITH_DL_MALLOC)
    set_property(DIRECTORY APPEND PROPERTY COMPILE_DEFINITIONS USE_DL_MALLOC=1)
elseif (WITH_YAP_MALLOC)
    set_property(DIRECTORY APPEND PROPERTY COMPILE_DEFINITIONS USE_YAP_MALLOC=1)
endif ()
check_include_file(alloca.h HAVE_ALLOCA_H)
check_include_file(apache2/util_md5.h HAVE_APACHE2_UTIL_MD5_H)
check_include_file(apr-1/apr_md5.h HAVE_APR_1_APR_MD5_H)
check_include_file(arpa/inet.h HAVE_ARPA_INET_H)
check_include_files(ctype.h HAVE_CTYPE_H)
check_include_file(direct.h HAVE_DIRECT_H)
check_include_file(dirent.h HAVE_DIRENT_H)
check_include_file(dlfcn.h HAVE_DLFCN_H)
check_include_file(errno.h HAVE_ERRNO_H)
check_include_file(execinfo.h HAVE_EXECINFO_H)
check_include_file(fcntl.h HAVE_FCNTL_H)
check_include_file(fenv.h HAVE_FENV_H)
check_include_files(fmemopen.h HAVE_FMEMOPEN_H)
check_include_file(fpu_control.h HAVE_FPU_CONTROL_H)
check_function_exists(gettid HAVE_GETTID) # gettid() actually doesn't exist by itself, one must call syscall(SYS_gettid); instead
check_symbol_exists(SYS_gettid sys/syscall.h HAVE_SYS_GETTID) #this only works if we force include syscall.h on the files that want to call gettid
check_include_file(glob.h HAVE_GLOB_H)
check_include_file(ieeefp.h HAVE_IEEEFP_H)
check_include_file(inttypes.h HAVE_INTTYPES_H)
check_include_file(io.h HAVE_IO_H)
check_include_file(libgen.h HAVE_LIBGEN_H)
check_include_file(LibLoaderAPI.h HAVE_LIBLOADERAPI_H)
check_include_file(limits.h HAVE_LIMITS_H)
check_include_file(locale.h HAVE_LOCALE_H)
check_include_file(mach-o/dyld.h HAVE_MACH_O_DYLD_H)
check_include_file(malloc.h HAVE_MALLOC_H)
check_include_file(math.h HAVE_MATH_H)
check_include_file(memory.h HAVE_MEMORY_H)
check_include_file(mpe.h HAVE_MPE_H)
check_include_file(mpi.h HAVE_MPI_H)
check_include_file(mysql/mysql.h HAVE_MYSQL_MYSQL_H)
check_include_file(netdb.h HAVE_NETDB_H)
check_include_file(netinet/in.h HAVE_NETINET_IN_H)
check_include_file(netinet/tcp.h HAVE_NETINET_TCP_H)
check_include_file(pthread.h HAVE_PTHREAD_H)
check_include_file(pwd.h HAVE_PWD_H)
check_include_file(regex.h HAVE_REGEX_H)
check_include_file(setjmp.h HAVE_SETJMP_H)
check_include_file(shlobj.h HAVE_SHLOBJ_H)
check_include_file(siginfo.h HAVE_SIGINFO_H)
check_include_file(signal.h HAVE_SIGNAL_H)
check_include_file(sqlite3.h HAVE_SQLITE3_H)
check_include_file(sql.h HAVE_SQL_H)
check_include_file(stdbool.h HAVE_STDBOOL_H)
check_include_file(stdint.h HAVE_STDINT_H)
check_include_file(strings.h HAVE_STRINGS_H)
check_include_file(stropts.h HAVE_STROPTS_H)
check_include_file(syslog.h HAVE_SYSLOG_H)
check_include_file(sys/conf.h HAVE_SYS_CONF_H)
check_include_file(sys/dir.h HAVE_SYS_DIR_H)
check_include_file(sys/file.h HAVE_SYS_FILE_H)
check_include_file(sys/mman.h HAVE_SYS_MMAN_H)
check_include_file(sys/ndir.h HAVE_SYS_NDIR_H)
check_include_file(sys/param.h HAVE_SYS_PARAM_H)
check_include_file(sys/resource.h HAVE_SYS_RESOURCE_H)
check_include_file(sys/select.h HAVE_SYS_SELECT_H)
check_include_file(sys/shm.h HAVE_SYS_SHM_H)
check_include_file(sys/socket.h HAVE_SYS_SOCKET_H)
check_include_file(sys/stat.h HAVE_SYS_STAT_H)
check_include_file(sys/syscall.h HAVE_SYS_SYSCALL_H)
check_include_file(sys/times.h HAVE_SYS_TIMES_H)
check_include_file(sys/time.h HAVE_SYS_TIME_H)
check_include_file(sys/types.h HAVE_SYS_TYPES_H)
check_include_file(sys/ucontext.h HAVE_SYS_UCONTEXT_H)
check_include_file(sys/un.h HAVE_SYS_UN_H)
check_include_file(sys/wait.h HAVE_SYS_WAIT_H)
check_include_file(termios.h HAVE_TERMIOS_H)
check_include_file(time.h HAVE_TIME_H)
check_include_file(ucontext.h HAVE_UCONTEXT_H)
check_include_file(unistd.h HAVE_UNISTD_H)
check_include_file(util.h HAVE_UTIL_H)
check_include_file(utime.h HAVE_UTIME_H)
check_include_file(wchar.h HAVE_WCHAR_H)
check_include_file(wctype.h HAVE_WCTYPE_H)
check_include_file(windef.h HAVE_WINDEF_H)
check_include_file(windows.h HAVE_WINDOWS_H)
check_include_file(winsock2.h HAVE_WINSOCK2_H)
check_include_file(winsock.h HAVE_WINSOCK_H)
check_include_file(wordexp.h HAVE_WORDEXP_H)

check_include_file(Python.h HAVE_PYTHON_H)

check_type_size("short int" SIZEOF_SHORT_INT)
check_type_size("int" SIZEOF_INT)
check_type_size("long int" SIZEOF_LONG)
check_type_size("long int" SIZEOF_LONG_INT)
check_type_size("long long int" SIZEOF_LONG_LONG)
check_type_size("long long int" SIZEOF_LONG_LONG_INT)
check_type_size("float" SIZEOF_FLOAT)
check_type_size("double" SIZEOF_DOUBLE)
check_type_size("void *" SIZEOF_VOID_P)
check_type_size("void *" SIZEOF_VOIDP)
check_type_size("int *" SIZEOF_INT_P)
check_type_size("uintptr_t" CELLSIZE)
check_type_size("wchar_t" SIZEOF_WCHAR_T)

check_library_exists(android main "" HAVE_LIBANDROID)
if (HAVE_LIBANDROID)
    set(EXTRALIBS ${EXTRALIBS} android)
endif (HAVE_LIBANDROID)

find_library(HAVE_LIBM m)
if (HAVE_LIBM)
    target_link_libraries(libYap m)
    set(EXTRALIBS ${EXTRALIBS} m)
endif (HAVE_LIBM)

check_library_exists(dl dlopen "" HAVE_LIBDL)
if (HAVE_LIBDL)
    target_link_libraries(libYap dl)
    set(CMAKE_REQUIRED_LIBRARIES ${CMAKE_REQUIRED_LIBRARIES} dl)
    set(HAVE_DLOPEN 1)
endif (HAVE_LIBDL)

if (WIN32)
    check_library_exists(comdlg32 FindText "" HAVE_LIBCOMDLG32)
    #if (HAVE_LIBCOMDLG32)

        set(WINDLLS ${WINDLLS} comdlg32)
    #endif (HAVE_LIBCOMDLG32)
    check_library_exists(msvcrt strtok "" HAVE_LIBMSCRT)

#if (HAVE_LIBMSCRT)
        set(WINDLLS ${WINDLLS} mscrt)
    #endif (HAVE_LIBMSCRT)
    check_library_exists(shell32 main "" HAVE_LIBSHELL32)

    #if (HAVE_LIBSHELL32)
        set(WINDLLS ${WINDLLS} shell32)
    #endif (HAVE_LIBSHELL32)

    check_library_exists(wsock32 main "" HAVE_LIBWSOCK32)
    #if (HAVE_LIBWSOCK32)
        set(WINDLLS ${WINDLLS} wsock32)
    #endif (HAVE_LIBWSOCK32)

    check_library_exists(ws2_32 main "" HAVE_LIBWS2_32)
    #if (HAVE_LIBWS2_32 OR TRUE)
        set(WINDLLS ${WINDLLS} ws2_32)
    #endif (HAVE_LIBWS2_32)
endif ()

check_library_exists(judy Judy1Set "" HAVE_LIBJUDY)
if (HAVE_LIBJUDY)
endif (HAVE_LIBJUDY)

check_library_exists(log main "" HAVE_LIBLOG)
if (HAVE_LIBLOG)
endif (HAVE_LIBLOG)

# check_library_exists( nsl nis_add "" HAVE_LIBNSL )
# if (HAVE_LIBNSL)
#   target_link_libraries(libYap nsl)
# endif (HAVE_LIBNSL)

# check_library_exists( nss_dns main "" HAVE_LIBNSS_DNS )
# if (HAVE_LIBNSS_DNS)
#   target_link_libraries(libYap nss_dns)
# endif (HAVE_LIBNSS_DNS)

# check_library_exists( nss_files main "" HAVE_LIBNSS_FILES )
# if (HAVE_LIBNSS_FILES)
#   set(EXTRALIBS ${EXTRALIBS} nss_files)
# endif (HAVE_LIBNSS_FILES)

# check_library_exists( psapi main "" HAVE_LIBPSAPI )
# if (HAVE_LIBPSAPI)
#   set(EXTRALIBS ${EXTRALIBS} psapi)
# endif (HAVE_LIBPSAPI)

# check_library_exists( resolv main "" HAVE_LIBRESOLV )
# if (HAVE_LIBRESOLV)
#   set(EXTRALIBS ${EXTRALIBS} resolv)
# endif (HAVE_LIBRESOLV)


# check_library_exists( socket socket "" HAVE_LIBSOCKET )
# if (HAVE_LIBSOCKET)
#   set(EXTRALIBS ${EXTRALIBS} socket)
# endif (HAVE_LIBSOCKET)

find_library(HAVE_LIBPTHREAD pthread)
if (HAVE_LIBPTHREAD)
    target_link_libraries(libYap pthread)
    set(EXTRALIBS ${EXTRALIBS} pthread)
  endif (HAVE_LIBPTHREAD)



check_library_exists(unicode main "" HAVE_LIBUNICODE)
if (HAVE_LIBUNICODE)
    set(EXTRALIBS ${EXTRALIBS} unicode)
endif (HAVE_LIBUNICODE)

check_library_exists(xnet main "" HAVE_LIBXNET)
if (HAVE_LIBXNET)
    set(EXTRALIBS ${EXTRALIBS} xnet)
endif (HAVE_LIBXNET)


check_function_exists(_NSGetEnviron HAVE__NSGETENVIRON)
check_function_exists(access HAVE_ACCESS)
check_function_exists(acosh HAVE_ACOSH)
check_function_exists(asinh HAVE_ASINH)
check_function_exists(atanh HAVE_ATANH)
check_function_exists(backtrace HAVE_BACKTRACE)
check_function_exists(basename HAVE_BASENAME)
check_function_exists(chdir HAVE_CHDIR)
check_function_exists(_chsize_s HAVE__CHSIZE_S)
check_function_exists(clock HAVE_CLOCK)
check_function_exists(clock_gettime HAVE_CLOCK_GETTIME)
check_function_exists(ctime HAVE_CTIME)
check_function_exists(dlopen HAVE_DLOPEN)
check_function_exists(dup2 HAVE_DUP2)
check_function_exists(dynarray HAVE_DYNARRAY)
check_function_exists(environ HAVE_ENVIRON)
check_function_exists(erf HAVE_ERF)
check_function_exists(feclearexcept HAVE_FECLEAREXCEPT)
check_function_exists(feenableexcept HAVE_FEENABLEEXCEPT)
check_function_exists(fesetexceptflag HAVE_FESETEXCEPTFLAG)
check_function_exists(fesetround HAVE_FESETROUND)
check_function_exists(fesettrapenable HAVE_FESETTRAPENABLE)
check_function_exists(fetestexcept HAVE_FETESTEXCEPT)
check_symbol_exists(ffsl <string.h> HAVE_FFSL)
check_symbol_exists(ffsll <string.h> HAVE_FFSLL)
check_function_exists(__builtin_ffsll HAVE___BUILTIN_FFSLL)
check_function_exists(fgetpos HAVE_FGETPOS)
check_function_exists(finite HAVE_FINITE)
check_function_exists(iswblank HAVE_ISWBLANK)
check_function_exists(iswspace HAVE_ISWSPACE)
check_symbol_exists(flsl <string.h> HAVE_FLSL)
check_symbol_exists(flsll <string.h> HAVE_FLSLL)
if (NOT APPLE)
  # only recently available
  check_function_exists(fmemopen HAVE_FMEMOPEN)
endif()
check_function_exists(fpclass HAVE_FPCLASS)
check_function_exists(fpurge HAVE_FPURGE)
check_function_exists(ftime HAVE_FTIME)
check_function_exists(ftruncate HAVE_FTRUNCATE)
check_function_exists(funopen HAVE_FUNOPEN)
#check_function_exists(gcc HAVE_GCC)
check_function_exists(getcwd HAVE_GETCWD)
check_function_exists(getenv HAVE_GETENV)
check_function_exists(getexecname HAVE_GETEXECNAME)
check_function_exists(gethostbyname HAVE_GETHOSTBYNAME)
check_function_exists(gethostent HAVE_GETHOSTENT)
check_function_exists(gethostid HAVE_GETHOSTID)
check_function_exists(gethostname HAVE_GETHOSTNAME)
check_function_exists(gethrtime HAVE_GETHRTIME)
check_function_exists(getpagesize HAVE_GETPAGESIZE)
check_function_exists(getpid HAVE_GETPID)
check_function_exists(getpwnam HAVE_GETPWNAM)
check_function_exists(getrlimit HAVE_GETRLIMIT)
check_function_exists(getrusage HAVE_GETRUSAGE)
check_function_exists(gettimeofday HAVE_GETTIMEOFDAY)
check_function_exists(getwd HAVE_GETWD)
check_function_exists(glob HAVE_GLOB)
check_function_exists(gmtime HAVE_GMTIME)
check_function_exists(h_errno HAVE_H_ERRNO)
check_function_exists(isatty HAVE_ISATTY)
check_function_exists(isfinite HAVE_ISFINITE)
check_function_exists(isinf HAVE_ISINF)
check_function_exists(isnan HAVE_ISNAN)
check_function_exists(kill HAVE_KILL)
check_function_exists(labs HAVE_LABS)
check_function_exists(link HAVE_LINK)
check_function_exists(localtime HAVE_LOCALTIME)
check_function_exists(lstat HAVE_LSTAT)
check_symbol_exists(mallinfo " malloc.h" HAVE_MALLINFO)
check_function_exists(mbscoll HAVE_MBSCOLL)
check_function_exists(mbscasecoll HAVE_MBSCASECOLL)
check_function_exists(mbsnrtowcs HAVE_MBSNRTOWCS)
check_function_exists(memmove HAVE_MEMCPY)
check_function_exists(memmove HAVE_MEMMOVE)
check_function_exists(mkstemp HAVE_MKSTEMP)
check_function_exists(mktemp HAVE_MKTEMP)
check_function_exists(nanosleep HAVE_NANOSLEEP)
check_function_exists(mktime HAVE_MKTIME)
check_function_exists(mtrace HAVE_MTRACE)
check_function_exists(opendir HAVE_OPENDIR)
if (NOT APPLE)
  check_function_exists(open_memstream HAVE_OPEN_MEMSTREAM)
  endif()
check_function_exists(putenv HAVE_PUTENV)
check_function_exists(rand HAVE_RAND)
check_function_exists(random HAVE_RANDOM)
check_function_exists(readlink HAVE_READLINK)
check_function_exists(realpath HAVE_REALPATH)
check_function_exists(regexec HAVE_REGEXEC)
check_function_exists(rename HAVE_RENAME)
check_function_exists(restartable_syscalls HAVE_RESTARTABLE_SYSCALLS)
check_function_exists(rint HAVE_RINT)
check_function_exists(sbrk HAVE_SBRK)
check_function_exists(select HAVE_SELECT)
check_function_exists(setbuf HAVE_SETBUF)
check_function_exists(setitimer HAVE_SETITIMER)
check_function_exists(setlinebuf HAVE_SETLINEBUF)
check_function_exists(setlocale HAVE_SETLOCALE)
check_function_exists(setsid HAVE_SETSID)
check_function_exists(shmat HAVE_SHMAT)
check_function_exists(sigaction HAVE_SIGACTION)
check_symbol_exists(SIGFPE signal.h HAVE_SIGFPE)
check_function_exists(siggetmask HAVE_SIGGETMASK)
check_symbol_exists(SIGINFO signal.h HAVE_SIGINFO)
check_function_exists(siginterrupt HAVE_SIGINTERRUPT)
check_function_exists(signal HAVE_SIGNAL)
check_function_exists(sigprocmask HAVE_SIGPROCMASK)
check_symbol_exists(SIGPROF signal.h HAVE_SIGPROF)
check_symbol_exists(SIGSEGV signal.h HAVE_SIGSEGV)
check_symbol_exists(sigsetjmp setjmp.h HAVE_SIGSETJMP)
check_function_exists(sleep HAVE_SLEEP)
check_function_exists(snprintf HAVE_SNPRINTF)
check_function_exists(socket HAVE_SOCKET)
check_function_exists(socklen_t HAVE_SOCKLEN_T)
check_function_exists(sqllen HAVE_SQLLEN)
check_function_exists(sqlulen HAVE_SQLULEN)
check_function_exists(srand HAVE_SRAND)
check_function_exists(srand48 HAVE_SRAND48)
check_function_exists(srandom HAVE_SRANDOM)
check_function_exists(stpcpy HAVE_STPCPY)
check_function_exists(stpncpy HAVE_STPNCPY)
check_function_exists(ssize_t HAVE_SSIZE_T)
check_function_exists(stat HAVE_STAT)
check_function_exists(strcat HAVE_STRCAT)
check_function_exists(strncat HAVE_STRNCAT)
check_function_exists(strcasecmp HAVE_STRCASECMP)
check_function_exists(strcasestr HAVE_STRCASESTR)
check_function_exists(strchr HAVE_STRCHR)
check_function_exists(strerror HAVE_STRERROR)
check_function_exists(stricmp HAVE_STRICMP)
check_function_exists(strlcpy HAVE_STRLCPY)
check_function_exists(strlwr HAVE_STRLWR)
check_function_exists(strncasecmp HAVE_STRNCASECMP)
check_function_exists(strncat HAVE_STRNCAT)
check_function_exists(strncpy HAVE_STRNCPY)
check_function_exists(strnlen HAVE_STRNLEN)
check_function_exists(strtod HAVE_STRTOD)
check_function_exists(struct_time_tm_gmtoff HAVE_STRUCT_TIME_TM_GMTOFF)
check_function_exists(system HAVE_SYSTEM)
check_function_exists(tcflush HAVE_TCFLUSH)
check_function_exists(time HAVE_TIME)
check_function_exists(timegm HAVE_TIMEGM)
check_function_exists(times HAVE_TIMES)
check_symbol_exists(timezone time.h HAVE_VAR_TIMEZONE)
check_function_exists(tmpnam HAVE_TMPNAM)
check_function_exists(ttyname HAVE_TTYNAME)
check_function_exists(usleep HAVE_USLEEP)
check_function_exists(utime HAVE_UTIME)
check_function_exists(var_timezone HAVE_VAR_TIMEZONE)
check_function_exists(vfork HAVE_VFORK)
check_function_exists(vsnprintf HAVE_VSNPRINTF)
check_function_exists(waitpid HAVE_WAITPID)
check_function_exists(wcsdup HAVE_WCSDUP)
check_function_exists(wcsnlen HAVE_WCSNLEN)
check_function_exists(wordexp HAVE_WORDEXP)
check_function_exists(_bool HAVE__BOOL)
check_function_exists(_chsize_s HAVE__CHSIZE_S)
check_function_exists(_NSGetEnviron HAVE__NSGETENVIRON)

check_symbol_exists(__NR_gettid "sys/syscall.h;unistd.h" HAVE_GETTID_SYSCALL)
check_symbol_exists(gettid "sys/syscall.h;unistd.h" HAVE_GETTID_MACRO)

if (CMAKE_SIZEOF_VOID_P EQUAL 8)
    set(bitness 64)
else ()
    set(bitness 32)
endif ()

get_git_head_revision(GIT_HEAD GIT_SHA1)
git_describe(GIT_DESCRIBE)

#Test standard headers (mimics AC_HEADER_STDC)
include(TestSTDC)

if (WITH_READLINE)

check_include_files( "stdio.h;readline/readline.h" HAVE_READLINE_READLINE_H )
check_include_files( "stdio.h;readline/history.h"  HAVE_READLINE_HISTORY_H )
check_function_exists( add_history  HAVE_ADD_HISTORY )
check_function_exists( rl_begin_undo_group HAVE_RL_BEGIN_UNDO_GROUP)
check_function_exists( rl_clear_pending_input HAVE_RL_CLEAR_PENDING_INPUT)
check_function_exists( rl_discard_argument HAVE_RL_DISCARD_ARGUMENT)
check_symbol_exists( rl_filename_completion_function  stdio.h;readline/readline.h HAVE_RL_FILENAME_COMPLETION_FUNCTION)
check_function_exists( rl_free_line_state HAVE_RL_FREE_LINE_STATE )
check_function_exists( rl_insert_close  HAVE_RL_INSERT_CLOSE )
check_function_exists( rl_reset_after_signal  HAVE_RL_RESET_AFTER_SIGNAL )
check_function_exists( rl_set_keyboard_input_timeout  HAVE_RL_SET_KEYBOARD_INPUT_TIMEOUT )
check_function_exists( rl_set_prompt  HAVE_RL_SET_PROMPT)
check_function_exists( rl_set_signals  HAVE_RL_SET_SIGNALS)
check_symbol_exists( rl_catch_signals "stdio.h;readline/readline.h"   HAVE_DECL_RL_CATCH_SIGNALS )
check_type_size( rl_completion_func_t RL_COMPLETION_FUNC_T    )
check_symbol_exists( rl_done stdio.h;readline/readline.h  HAVE_DECL_RL_DONE )
CHECK_TYPE_SIZE( rl_hook_func_t  RL_HOOK_FUNC_T  )
check_symbol_exists( rl_event_hook stdio.h;readline/readline.h HAVE_DECL_RL_EVENT_HOOK )
check_symbol_exists( rl_readline_state stdio.h;readline/readline.h HAVE_DECL_RL_READLINE_STATE )
check_function_exists( add_history HAVE_ADD_HISTORY)
check_function_exists( remove_history HAVE_REMOVE_HISTORY)
check_function_exists( using_history HAVE_USING_HISTORY)
endif()

configure_file(${CMAKE_SOURCE_DIR}/os/YapIOConfig.h.cmake ${CMAKE_BINARY_DIR}/YapIOConfig.h)
configure_file(${CMAKE_CURRENT_LIST_DIR}/../config.h.cmake
        ${CMAKE_BINARY_DIR}/YapConfig.h)
configure_file(${CMAKE_CURRENT_LIST_DIR}/../YapTermConfig.h.cmake
        ${CMAKE_BINARY_DIR}/YapTermConfig.h)
configure_file(${CMAKE_CURRENT_LIST_DIR}/../config.h.cmake
        ${CMAKE_BINARY_DIR}/config.h)
configure_file(${CMAKE_CURRENT_LIST_DIR}/../GitSHA1.c.in GitSHA1.c @ONLY)
