/*************************************************************************
*									 *
*	 YAP Prolog 							 *
*									 *
*	Yap Prolog was developed at NCCUP - Universidade do Porto	 *
*									 *
* Copyright L.Damas, V.S.Costa and Universidade do Porto 1985-1997	 *
*									 *
**************************************************************************
*									 *
* $Id: sys.c,v 1.17 2004-01-26 12:41:06 vsc Exp $									 *
* mods:		$Log: not supported by cvs2svn $
* mods:		Revision 1.16  2003/01/27 15:55:40  vsc
* mods:		use CVS Id
* mods:		
* mods:		Revision 1.15  2003/01/27 15:54:10  vsc
* mods:		fix header
* mods:									 *
* comments:	regular expression interpreter                           *
*									 *
*************************************************************************/

#include "config.h"
#include "YapInterface.h"
#if STDC_HEADERS
#include <stdlib.h>
#endif
#if HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <stdio.h>
#if HAVE_TIME_H
#include <time.h>
#endif
#if HAVE_SYS_TYPES_H
#include <sys/types.h>
#endif
#if HAVE_SYS_STAT_H
#include <sys/stat.h>
#endif
#if HAVE_FCNTL_H
#include <fcntl.h>
#endif
#if HAVE_UNISTD_H
#include <unistd.h>
#endif
#if HAVE_ERRNO_H
#include <errno.h>
#endif
#if HAVE_STRING_H
#include <string.h>
#endif
#if HAVE_SIGNAL_H
#include <signal.h>
#endif
#if HAVE_SYS_WAIT_H
#include <sys/wait.h>
#endif
#if HAVE_DIRENT_H
#include <dirent.h>
#endif
#if HAVE_DIRECT_H
#include <direct.h>
#endif
#if defined(__MINGW32__) || _MSC_VER
#include <windows.h>
#include <process.h>
#endif
#ifdef __MINGW32__
#ifdef HAVE_ENVIRON
#undef HAVE_ENVIRON
#endif
#endif

void PROTO(init_sys, (void));

#if defined(__MINGW32__) || _MSC_VER
static YAP_Term
WinError(void)
{
  char msg[256];
  /* Error, we could not read time */
    FormatMessage(FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS,
		  NULL, GetLastError(), 
		  MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT), msg, 256,
		  NULL);
    return(YAP_MkAtomTerm(YAP_LookupAtom(msg)));
}
#endif

/* Return time in a structure */
static int
datime(void)
{
  YAP_Term tf, out[6];
#if defined(__MINGW32__) || _MSC_VER
  SYSTEMTIME stime;
  GetLocalTime(&stime);
  out[0] = YAP_MkIntTerm(stime.wYear);
  out[1] = YAP_MkIntTerm(stime.wMonth);
  out[2] = YAP_MkIntTerm(stime.wDay);
  out[3] = YAP_MkIntTerm(stime.wHour);
  out[4] = YAP_MkIntTerm(stime.wMinute);
  out[5] = YAP_MkIntTerm(stime.wSecond);
#elif HAVE_TIME
  time_t  tp;

  if ((tp = time(NULL)) == -1) {
     return(YAP_Unify(YAP_ARG2, YAP_MkIntTerm(errno)));    
  }
#ifdef HAVE_LOCALTIME
 {
   struct tm *loc = localtime(&tp);
   if (loc == NULL) {
     return(YAP_Unify(YAP_ARG2, YAP_MkIntTerm(errno)));    
   }
   out[0] = YAP_MkIntTerm(1900+loc->tm_year);
   out[1] = YAP_MkIntTerm(1+loc->tm_mon);
   out[2] = YAP_MkIntTerm(loc->tm_mday);
   out[3] = YAP_MkIntTerm(loc->tm_hour);
   out[4] = YAP_MkIntTerm(loc->tm_min);
   out[5] = YAP_MkIntTerm(loc->tm_sec);
 }
#else
  oops
#endif /* HAVE_LOCALTIME */
#else
  oops
#endif /* HAVE_TIME */
  tf = YAP_MkApplTerm(YAP_MkFunctor(YAP_LookupAtom("date"),6), 6, out);
  return(YAP_Unify(YAP_ARG1, tf));
}

#define BUF_SIZE 1024

/* Return a list of files for a directory */
static int
list_directory(void)
{
  YAP_Term tf = YAP_MkAtomTerm(YAP_LookupAtom("[]"));

  char *buf = YAP_AtomName(YAP_AtomOfTerm(YAP_ARG1));
#if defined(__MINGW32__) || _MSC_VER
  struct _finddata_t c_file;
  char bs[BUF_SIZE];
  long hFile;

  bs[0] = '\0';
#if HAVE_STRNCPY
  strncpy(bs, buf, BUF_SIZE);
#else
  strcpy(bs, buf);
#endif
#if HAVE_STRNCAT
  strncat(bs, "/*", BUF_SIZE);
#else
  strncat(bs, "/*");
#endif
  if ((hFile = _findfirst(bs, &c_file)) == -1L) {
    return(YAP_Unify(YAP_ARG2,tf));
  }
  tf = YAP_MkPairTerm(YAP_MkAtomTerm(YAP_LookupAtom(c_file.name)), tf);
  while (_findnext( hFile, &c_file) == 0) {
    YAP_Term ti = YAP_MkAtomTerm(YAP_LookupAtom(c_file.name));
    tf = YAP_MkPairTerm(ti, tf);
  }
  _findclose( hFile );
#else
#if HAVE_OPENDIR
 {
   DIR *de;
   struct dirent *dp;

   if ((de = opendir(buf)) == NULL) {
     return(YAP_Unify(YAP_ARG3, YAP_MkIntTerm(errno)));
   }
   while ((dp = readdir(de))) {
     YAP_Term ti = YAP_MkAtomTerm(YAP_LookupAtom(dp->d_name));
     tf = YAP_MkPairTerm(ti, tf);
   }
   closedir(de);
 }
#endif /* HAVE_OPENDIR */
#endif
  return(YAP_Unify(YAP_ARG2, tf));
}

static int
p_unlink(void)
{
  char *fd = YAP_AtomName(YAP_AtomOfTerm(YAP_ARG1));
#if defined(__MINGW32__) || _MSC_VER
  if (_unlink(fd) == -1)
#else
  if (unlink(fd) == -1)
#endif
    {
      /* return an error number */
      return(YAP_Unify(YAP_ARG2, YAP_MkIntTerm(errno)));
    }
  return(TRUE);
}

static int
p_mkdir(void)
{
  char *fd = YAP_AtomName(YAP_AtomOfTerm(YAP_ARG1));
#if defined(__MINGW32__) || _MSC_VER
  if (_mkdir(fd) == -1) {
#else
  if (mkdir(fd, 0777) == -1) {
#endif
    /* return an error number */
    return(YAP_Unify(YAP_ARG2, YAP_MkIntTerm(errno)));
  }
  return(TRUE);
}

static int
p_rmdir(void)
{
  char *fd = YAP_AtomName(YAP_AtomOfTerm(YAP_ARG1));
#if defined(__MINGW32__) || _MSC_VER
  if (_rmdir(fd) == -1) {
#else
  if (rmdir(fd) == -1) {
#endif
    /* return an error number */
    return(YAP_Unify(YAP_ARG2, YAP_MkIntTerm(errno)));
  }
  return(TRUE);
}

static int
rename_file(void)
{
  char *s1 = YAP_AtomName(YAP_AtomOfTerm(YAP_ARG1));
  char *s2 = YAP_AtomName(YAP_AtomOfTerm(YAP_ARG2));
#if HAVE_RENAME
  if (rename(s1, s2) == -1) {
    /* return an error number */
    return(YAP_Unify(YAP_ARG3, YAP_MkIntTerm(errno)));
  }
#endif
  return(TRUE);
}

static int
dir_separator(void)
{
  return(YAP_Unify(YAP_ARG1,YAP_MkAtomTerm(YAP_LookupAtom("/"))));
}

static int
file_property(void)
{
  char *fd;
#if HAVE_LSTAT 
  struct stat buf;

  fd = YAP_AtomName(YAP_AtomOfTerm(YAP_ARG1));
  if (lstat(fd, &buf) == -1) {
    /* return an error number */
    return(YAP_Unify(YAP_ARG7, YAP_MkIntTerm(errno)));
  }
  if (S_ISREG(buf.st_mode)) {
    if (!(YAP_Unify(YAP_ARG2, YAP_MkAtomTerm(YAP_LookupAtom("regular"))) &&
	  YAP_Unify(YAP_ARG6, YAP_MkIntTerm(0))))
      return(FALSE);
  } else if (S_ISDIR(buf.st_mode)) {
    if (!(YAP_Unify(YAP_ARG2, YAP_MkAtomTerm(YAP_LookupAtom("directory"))) &&
	  YAP_Unify(YAP_ARG6, YAP_MkIntTerm(0))))
      return(FALSE);
  } else if (S_ISFIFO(buf.st_mode)) {
    if (!(YAP_Unify(YAP_ARG2, YAP_MkAtomTerm(YAP_LookupAtom("fifo"))) &&
	  YAP_Unify(YAP_ARG6, YAP_MkIntTerm(0))))
      return(FALSE);
  } else if (S_ISLNK(buf.st_mode)) {
    if (!YAP_Unify(YAP_ARG2, YAP_MkAtomTerm(YAP_LookupAtom("symlink"))))
      return(FALSE);
#if HAVE_READLINK
    {
      char tmp[256];
      int n;
      if ((n = readlink(fd,tmp,256)) == -1) {
	return(YAP_Unify(YAP_ARG7, YAP_MkIntTerm(errno)));
      }
      tmp[n] = '\0';
      if(!YAP_Unify(YAP_ARG6,YAP_MkAtomTerm(YAP_LookupAtom(tmp)))) {
	return(FALSE);
      }
    }
#else
    if (!YAP_Unify(YAP_ARG6, YAP_MkIntTerm(0)))
      return(FALSE);
#endif    
  } else if (S_ISSOCK(buf.st_mode)) {
    if (!(YAP_Unify(YAP_ARG2, YAP_MkAtomTerm(YAP_LookupAtom("socket"))) &&
	  YAP_Unify(YAP_ARG6, YAP_MkIntTerm(0))))
      return(FALSE);
  } else {
    if (!(YAP_Unify(YAP_ARG2, YAP_MkAtomTerm(YAP_LookupAtom("unknown"))) &&
	  YAP_Unify(YAP_ARG6, YAP_MkIntTerm(0))))
      return(FALSE);
  }
#elif defined(__MINGW32__) || _MSC_VER
  /* for some weird reason _stat did not work with mingw32 */
  struct _stat buf;

  fd = YAP_AtomName(YAP_AtomOfTerm(YAP_ARG1));
  if (_stat(fd, &buf) != 0) {
    /* return an error number */
    return(YAP_Unify(YAP_ARG7, YAP_MkIntTerm(errno)));
  }
  if (buf.st_mode & S_IFREG) {
    if (!YAP_Unify(YAP_ARG2, YAP_MkAtomTerm(YAP_LookupAtom("regular"))))
      return(FALSE);
  } else if (buf.st_mode & S_IFDIR) {
    if (!YAP_Unify(YAP_ARG2, YAP_MkAtomTerm(YAP_LookupAtom("directory"))))
      return(FALSE);
  } else {
    if (!YAP_Unify(YAP_ARG2, YAP_MkAtomTerm(YAP_LookupAtom("unknown"))))
      return(FALSE);
  }
#endif
  return (
	  YAP_Unify(YAP_ARG3, YAP_MkIntTerm(buf.st_size)) &&
	  YAP_Unify(YAP_ARG4, YAP_MkIntTerm(buf.st_mtime)) &&
	  YAP_Unify(YAP_ARG5, YAP_MkIntTerm(buf.st_mode))
	  );
}

/* temporary files */

static int
p_mktemp(void)
{
#if HAVE_MKTEMP
  char *s, tmp[BUF_SIZE];
  s = YAP_AtomName(YAP_AtomOfTerm(YAP_ARG1));
#if HAVE_STRNCPY
  strncpy(tmp, s, BUF_SIZE);
#else
  strcpy(tmp, s);
#endif
#if defined(__MINGW32__) || _MSC_VER
  if ((s = _mktemp(tmp)) == NULL) {
#else
  if ((s = mktemp(tmp)) == NULL) {
#endif
    /* return an error number */
    return(YAP_Unify(YAP_ARG3, YAP_MkIntTerm(errno)));
  }
  return(YAP_Unify(YAP_ARG2,YAP_MkAtomTerm(YAP_LookupAtom(s))));
#else
 oops
#endif
  return(TRUE); 
}

static int
p_tpmnam(void)
{
#if HAVE_TMPNAM
  return(YAP_Unify(YAP_ARG1,YAP_MkAtomTerm(YAP_LookupAtom(tmpnam(NULL)))));
#else
oops
#endif
}

/* return YAP's environment */
static int
p_environ(void)
{
#if HAVE_ENVIRON
#if defined(__MINGW32__) || _MSC_VER
  extern char **_environ;
#else
  extern char **environ;
#endif
  YAP_Term t1 = YAP_ARG1;
  long int i;

  i = YAP_IntOfTerm(t1);
#if defined(__MINGW32__) || _MSC_VER
  if (_environ[i] == NULL)
#else
  if (environ[i] == NULL)
#endif
    return(FALSE);
  else {
    YAP_Term t = YAP_BufferToString(environ[i]);
    return(YAP_Unify(t, YAP_ARG2));
  }
#else
  YAP_Error("environ not available in this configuration");
  return(FALSE);
#endif
}

#if defined(__MINGW32__) || _MSC_VER
static HANDLE
get_handle(YAP_Term ti, DWORD fd)
{
  if (YAP_IsAtomTerm(ti)) {
    HANDLE out;
    SECURITY_ATTRIBUTES satt;
    
    satt.nLength = sizeof(satt);
    satt.lpSecurityDescriptor = NULL;
    satt.bInheritHandle = TRUE;
    out = CreateFile("NUL",
			    GENERIC_READ|GENERIC_WRITE,
			    FILE_SHARE_READ|FILE_SHARE_WRITE,
			    &satt,
			    OPEN_EXISTING,
			    0,
			    NULL);
    return(out);
  } else {
    if (YAP_IsIntTerm(ti)) {
      return(GetStdHandle(fd));
    } else
      return((HANDLE)YAP_StreamToFileNo(ti));
  }
}

static void
close_handle(YAP_Term ti, HANDLE h)
{
  if (YAP_IsAtomTerm(ti)) {
    CloseHandle(h);
  }
}

#endif

/* execute a command as a detached process */
static int
execute_command(void)
{
  YAP_Term ti = YAP_ARG2, to = YAP_ARG3, te = YAP_ARG4;
  int res;
#if defined(__MINGW32__) || _MSC_VER
  HANDLE inpf, outf, errf;
  DWORD CreationFlags = 0;
  STARTUPINFO StartupInfo;
  PROCESS_INFORMATION ProcessInformation;
  inpf = get_handle(ti, STD_INPUT_HANDLE);
  if (inpf == INVALID_HANDLE_VALUE) {
    return(YAP_Unify(YAP_ARG6, WinError()));
  }
  outf = get_handle(to, STD_OUTPUT_HANDLE);
  if (outf == INVALID_HANDLE_VALUE) {
    close_handle(ti, inpf);
    return(YAP_Unify(YAP_ARG6, WinError()));
  }
  errf = get_handle(te, STD_OUTPUT_HANDLE);
  if (errf == INVALID_HANDLE_VALUE) {
    close_handle(ti, inpf);
    close_handle(to, outf);
    return(YAP_Unify(YAP_ARG6, WinError()));
  }
  if (!YAP_IsIntTerm(ti) && !YAP_IsIntTerm(to) && !YAP_IsIntTerm(te)) {
    /* we do not keep a current stream */
    CreationFlags = DETACHED_PROCESS;
  }
  StartupInfo.cb = sizeof(STARTUPINFO);
  StartupInfo.lpReserved = NULL;
  StartupInfo.lpDesktop = NULL; /* inherit */
  StartupInfo.lpTitle = NULL; /* we do not create a new console window */
  StartupInfo.dwFlags = STARTF_USESTDHANDLES;
  StartupInfo.cbReserved2 = 0;
  StartupInfo.lpReserved2 = NULL;
  StartupInfo.hStdInput = inpf;
  StartupInfo.hStdOutput = outf;
  StartupInfo.hStdError = errf;
  /* got stdin, stdout and error as I like it */
  if (CreateProcess(NULL,
		    YAP_AtomName(YAP_AtomOfTerm(YAP_ARG1)),
		    NULL,
		    NULL,
		    TRUE,
		    CreationFlags,
		    NULL,
		    NULL,
		    &StartupInfo,
		    &ProcessInformation) == FALSE) {
    close_handle(ti, inpf);
    close_handle(to, outf);
    close_handle(te, errf);
    return(YAP_Unify(YAP_ARG6, WinError()));
  }
  close_handle(ti, inpf);
  close_handle(to, outf);
  close_handle(te, errf);
  res = ProcessInformation.dwProcessId;
  return(YAP_Unify(YAP_ARG5,YAP_MkIntTerm(res)));  
#else /* UNIX CODE */
  int inpf, outf, errf;
  /* process input first */
  if (YAP_IsAtomTerm(ti)) {
    inpf = open("/dev/null", O_RDONLY);
  } else {
    int sd;
    if (YAP_IsIntTerm(ti))
      sd = 0;
    else
      sd = YAP_StreamToFileNo(ti);
    inpf = dup(sd);
  }
  if (inpf < 0) {
    /* return an error number */
    return(YAP_Unify(YAP_ARG6, YAP_MkIntTerm(errno)));
  }
  /* then output stream */
  if (YAP_IsAtomTerm(to)) {
    outf = open("/dev/zero", O_WRONLY);
  } else {
    int sd;
    if (YAP_IsIntTerm(to))
      sd = 1;
    else
      sd = YAP_StreamToFileNo(to);
    outf = dup(sd);
  }
  if (outf < 0) {
    /* return an error number */
    close(inpf);
    return(YAP_Unify(YAP_ARG6, YAP_MkIntTerm(errno)));
  }
  /* then error stream */
  if (YAP_IsAtomTerm(te)) {
    errf = open("/dev/zero", O_WRONLY);
  } else {
    int sd;
    if (YAP_IsIntTerm(te))
      sd = 2;
    else
      sd = YAP_StreamToFileNo(te);
    errf = dup(sd);
  }
  if (errf < 0) {
    /* return an error number */
    close(inpf);
    close(outf);
    return(YAP_Unify(YAP_ARG6, YAP_MkIntTerm(errno)));
  }
  /* we are now ready to fork */
  if ((res = fork()) < 0) {
    /* close streams we don't need */
    close(inpf);
    close(outf);
    close(errf);
    /* return an error number */
    return(YAP_Unify(YAP_ARG6, YAP_MkIntTerm(errno)));
  } else if (res == 0) {
    char *argv[4];

    /* child */
    /* close current streams, but not std streams */
    YAP_CloseAllOpenStreams();
    close(0);
    dup(inpf);
    close(inpf);
    close(1);
    dup(outf);
    close(outf);
    close(2);
    dup(errf);
    close(errf);
    argv[0] = "sh";
    argv[1] = "-c";
    argv[2] = YAP_AtomName(YAP_AtomOfTerm(YAP_ARG1));
    argv[3] = NULL;
    execv("/bin/sh", argv);
    exit(127);
    /* we have the streams where we want them, just want to execute now */
  } else {
    close(inpf);
    close(outf);
    close(errf);
    return(YAP_Unify(YAP_ARG5,YAP_MkIntTerm(res)));
  }
#endif /* UNIX code */
}

/* execute a command as a detached process */
static int
do_system(void)
{
  char *command = YAP_AtomName(YAP_AtomOfTerm(YAP_ARG1));
#if HAVE_SYSTEM
  int sys = system(command);
  if (sys < 0) {
    return(YAP_Unify(YAP_ARG3,YAP_MkIntTerm(errno)));
  }
  return(YAP_Unify(YAP_ARG2, YAP_MkIntTerm(sys)));
#else
  YAP_Error("system not available in this configuration");
  return(FALSE);
#endif
}



/* execute a command as a detached process */
static int
do_shell(void)
{
#if defined(__MINGW32__) || _MSC_VER
  char *buf = YAP_AllocSpaceFromYap(BUF_SIZE);
  int sys;

  if (buf == NULL) {
    YAP_Error("No Temporary Space for Shell");
    return(FALSE);
  }
#if HAVE_STRNCPY
  strncpy(YAP_AtomName(YAP_AtomOfTerm(YAP_ARG1)), buf, BUF_SIZE);
  strncpy(" ", buf, BUF_SIZE);
  strncpy(YAP_AtomName(YAP_AtomOfTerm(YAP_ARG2)), buf, BUF_SIZE);
  strncpy(" ", buf, BUF_SIZE);
  strncpy(YAP_AtomName(YAP_AtomOfTerm(YAP_ARG3)), buf, BUF_SIZE);
#else
  strcpy(YAP_AtomName(YAP_AtomOfTerm(YAP_ARG1)), buf);
  strcpy(" ", buf);
  strcpy(YAP_AtomName(YAP_AtomOfTerm(YAP_ARG2)), buf);
  strcpy(" ", buf);
  strcpy(YAP_AtomName(YAP_AtomOfTerm(YAP_ARG3)), buf);
#endif
#if HAVE_SYSTEM
  sys = system(buf);
  YAP_FreeSpaceFromYap(buf);
  if (sys < 0) {
    return(YAP_Unify(YAP_ARG5,YAP_MkIntTerm(errno)));
  }
  return(YAP_Unify(YAP_ARG4, YAP_MkIntTerm(sys)));
#else
  YAP_Error("system not available in this configuration");
  return(FALSE);
#endif
#else
  char *cptr[4];
  int t;
  int sys;

  cptr[0]= YAP_AtomName(YAP_AtomOfTerm(YAP_ARG1));
  cptr[1]= YAP_AtomName(YAP_AtomOfTerm(YAP_ARG2));
  cptr[2]= YAP_AtomName(YAP_AtomOfTerm(YAP_ARG3));
  cptr[3]= NULL;
  t = fork();
  if (t < 0) {
    return(YAP_Unify(YAP_ARG5,YAP_MkIntTerm(errno)));
  } else if (t == 0) {
    t = execvp(YAP_AtomName(YAP_AtomOfTerm(YAP_ARG1)),cptr);
    return(t);
  } else {
    t = wait(&sys);
    if (t < 0) {
      return(YAP_Unify(YAP_ARG5,YAP_MkIntTerm(errno)));
    }
  }
  return(YAP_Unify(YAP_ARG4, YAP_MkIntTerm(sys)));
#endif
}

/* execute a command as a detached process */
static int
p_wait(void)
{
  long int pid = YAP_IntOfTerm(YAP_ARG1);
#if defined(__MINGW32__) || _MSC_VER
  HANDLE proc = OpenProcess(STANDARD_RIGHTS_REQUIRED|SYNCHRONIZE, FALSE, pid);
  DWORD ExitCode;
  if (proc == NULL) {
    return(YAP_Unify(YAP_ARG3, WinError()));
  }
  if (WaitForSingleObject(proc, INFINITE) == WAIT_FAILED) {
    return(YAP_Unify(YAP_ARG3, WinError()));
  }
  if (GetExitCodeProcess(proc, &ExitCode) == 0) {
    return(YAP_Unify(YAP_ARG3, WinError()));
  }
  CloseHandle(proc);
  return(YAP_Unify(YAP_ARG2, YAP_MkIntTerm(ExitCode)));
#else
  do {
    int status;

    /* check for interruptions */
    if (waitpid(pid, &status, 0) == -1) {
      if (errno != EINTR)
	return -1;
      return(YAP_Unify(YAP_ARG3, YAP_MkIntTerm(errno)));
    } else {
      return(YAP_Unify(YAP_ARG2, YAP_MkIntTerm(status)));
    }
  } while(TRUE);
#endif
}

/* execute a command as a detached process */
static int
p_popen(void)
{
  char *command = YAP_AtomName(YAP_AtomOfTerm(YAP_ARG1));
  long int mode = YAP_IntOfTerm(YAP_ARG2);
  FILE *pfd;
  YAP_Term tsno;
  int flags;
  
#if HAVE_POPEN
#if defined(__MINGW32__) || _MSC_VER
  /* This will only work for console applications. FIX */
  if (mode == 0)
    pfd = _popen(command, "r");
  else
    pfd = _popen(command, "w");
#else
  if (mode == 0)
    pfd = popen(command, "r");
  else
    pfd = popen(command, "w");
#endif
  if (pfd == NULL) {
    return(YAP_Unify(YAP_ARG4, YAP_MkIntTerm(errno)));    
  }
  if (mode == 0)
    flags = YAP_INPUT_STREAM | YAP_POPEN_STREAM;
  else
    flags = YAP_OUTPUT_STREAM | YAP_POPEN_STREAM;
  tsno = YAP_OpenStream((void *)pfd,
		       "pipe",
		       YAP_MkAtomTerm(YAP_LookupAtom("pipe")),
		       flags);
#endif
  return(YAP_Unify(YAP_ARG3, tsno));
}

static int
p_sleep(void)
{
  YAP_Term ts = YAP_ARG1;
  long int secs = 0, usecs = 0, out;
  if (YAP_IsIntTerm(ts)) {
    secs = YAP_IntOfTerm(ts);
  }  else if (YAP_IsFloatTerm(ts)) {
    double tfl = YAP_FloatOfTerm(ts);
    if (tfl > 1.0)
      secs = tfl;
    else
      usecs = tfl*1000;
  }
#if defined(__MINGW32__) || _MSC_VER
  if (secs) usecs = secs*1000;
  Sleep(usecs);
  out = 0;
#else
#if HAVE_USLEEP
  if (usecs > 0) {
    usleep(usecs);
    out = 0;
  } else
#endif
#if HAVE_SLEEP
    {
      out = sleep(secs);
    }
#endif
#endif /* defined(__MINGW32__) || _MSC_VER */
  return(YAP_Unify(YAP_ARG2, YAP_MkIntTerm(out)));
}

/* host info */

static int
host_name(void)
{
#if defined(__MINGW32__) || _MSC_VER
  char name[MAX_COMPUTERNAME_LENGTH+1];
  DWORD nSize = MAX_COMPUTERNAME_LENGTH+1;
  if (GetComputerName(name, &nSize) == 0) {
    return(YAP_Unify(YAP_ARG2, WinError()));
  }
#else
#if HAVE_GETHOSTNAME
  char name[256];
  if (gethostname(name, 256) == -1) {
    /* return an error number */
    return(YAP_Unify(YAP_ARG2, YAP_MkIntTerm(errno)));
  }
#endif
#endif /* defined(__MINGW32__) || _MSC_VER */
  return(YAP_Unify(YAP_ARG1, YAP_MkAtomTerm(YAP_LookupAtom(name))));
}

static int
host_id(void)
{
#if HAVE_GETHOSTID
  return(YAP_Unify(YAP_ARG1, YAP_MkIntTerm(gethostid())));
#else
  return(YAP_Unify(YAP_ARG1, YAP_MkIntTerm(0)));
#endif
}

static int
pid(void)
{
#if defined(__MINGW32__) || _MSC_VER
  return(YAP_Unify(YAP_ARG1, YAP_MkIntTerm(_getpid())));
#else
  return(YAP_Unify(YAP_ARG1, YAP_MkIntTerm(getpid())));
#endif
}

static int
win(void)
{
#if defined(__MINGW32__) || _MSC_VER
  return(TRUE);
#else
  return(FALSE);
#endif
}

static int
p_kill(void)
{
#if defined(__MINGW32__) || _MSC_VER
  /* Windows does not support cross-process signals, so we shall do the
     SICStus thing and assume that a signal to a process will
     always kill it */
  HANDLE proc = OpenProcess(STANDARD_RIGHTS_REQUIRED|PROCESS_TERMINATE, FALSE, YAP_IntOfTerm(YAP_ARG1));
  if (proc == NULL) {
    return(YAP_Unify(YAP_ARG3, WinError()));
  }
  if (TerminateProcess(proc, -1) == 0) {
    return(YAP_Unify(YAP_ARG3, WinError()));
  }
  CloseHandle(proc);
#else
  if (kill(YAP_IntOfTerm(YAP_ARG1), YAP_IntOfTerm(YAP_ARG2)) < 0) {
    /* return an error number */
    return(YAP_Unify(YAP_ARG3, YAP_MkIntTerm(errno)));
  }
#endif /* defined(__MINGW32__) || _MSC_VER */
  return(TRUE); 
}

static int
error_message(void)
{
#if HAVE_STRERROR
  return(YAP_Unify(YAP_ARG2,YAP_MkAtomTerm(YAP_LookupAtom(strerror(YAP_IntOfTerm(YAP_ARG1))))));
#else
#if HAVE_STRERROR
  return(YAP_Unify(YAP_ARG2,YAP_ARG1));
#endif
#endif
}

void
init_sys(void)
{
  YAP_UserCPredicate("datime", datime, 2);
  YAP_UserCPredicate("list_directory", list_directory, 3);
  YAP_UserCPredicate("file_property", file_property, 7);
  YAP_UserCPredicate("unlink", p_unlink, 2);
  YAP_UserCPredicate("mkdir", p_mkdir, 2);
  YAP_UserCPredicate("rmdir", p_rmdir, 2);
  YAP_UserCPredicate("dir_separator", dir_separator, 1);
  YAP_UserCPredicate("p_environ", p_environ, 2);
  YAP_UserCPredicate("exec_command", execute_command, 6);
  YAP_UserCPredicate("do_shell", do_shell, 5);
  YAP_UserCPredicate("do_system", do_system, 3);
  YAP_UserCPredicate("popen", p_popen, 4);
  YAP_UserCPredicate("wait", p_wait, 3);
  YAP_UserCPredicate("host_name", host_name, 2);
  YAP_UserCPredicate("host_id", host_id, 2);
  YAP_UserCPredicate("pid", pid, 2);
  YAP_UserCPredicate("kill", p_kill, 3);
  YAP_UserCPredicate("mktemp", p_mktemp, 3);
  YAP_UserCPredicate("tmpnam", p_tpmnam, 2);
  YAP_UserCPredicate("rename_file", rename_file, 3);
  YAP_UserCPredicate("sleep", p_sleep, 2);
  YAP_UserCPredicate("error_message", error_message, 2);
  YAP_UserCPredicate("win", win, 0);
}

#ifdef _WIN32

#include <windows.h>

int WINAPI PROTO(win_sys, (HANDLE, DWORD, LPVOID));

int WINAPI win_sys(HANDLE hinst, DWORD reason, LPVOID reserved)
{
  switch (reason) 
    {
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
