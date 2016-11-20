/**
 * Copyright (c) 2014, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the "hack" directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 *
 */


#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <limits.h>
#include <stdlib.h>

#ifdef __APPLE__
#include <fcntl.h> // for open, fcntl, F_GETPATH, O_EVTONLY, O_SYMLINK
#include <unistd.h> // for close
#endif

#define Val_none Val_int(0)

static value
Val_some( value v )
{
  CAMLparam1( v );
  CAMLlocal1( some );
  some = caml_alloc(1, 0);
  Store_field( some, 0, v );
  CAMLreturn( some );
}

CAMLprim value
hh_normpath(value input) {
#ifdef __APPLE__
  CAMLparam1(input);
  CAMLlocal1(output);
  char result[PATH_MAX];
  output = input;
  int fd = open(String_val(input), O_EVTONLY | O_SYMLINK);
  if (fd != -1) {
    if (fcntl(fd, F_GETPATH, result) != -1) {
      output = caml_copy_string(result);
    }
    close(fd);
  }
  CAMLreturn(output);
#else
  return input;
#endif
}

CAMLprim value
hh_realpath(value v) {
  char *input;
#ifndef _WIN32
  char output[PATH_MAX];
#else
  char output[_MAX_PATH];
#endif
  char *result;

  CAMLparam1(v);

  input = String_val(v);
#ifndef _WIN32
  result = realpath(input, output);
#else
  result = _fullpath(output, input, _MAX_PATH);
#endif
  if (result == NULL) {
    CAMLreturn(Val_none);
  } else {
    CAMLreturn(Val_some(caml_copy_string(output)));
  }
}
