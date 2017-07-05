void test() {
  typed_pointer res;
  char *s = "()";
  res = read_sexp(s);
  assert(eq(res, empty_list));

  s = " ( ) ";
  res = read_sexp(s);
  assert(eq(res, empty_list));

  s = "(())";
  res = read_sexp(s);
  assert(eq(car(res), empty_list));
  assert(eq(cdr(res), empty_list));

  s = "(abcd (() 2 3))";
  res = read_sexp(s);
  char *r = sexp_to_str(res);
  assert(strcmp(r, s) == 0);
  free(r);

  res = make_pair();
  set_car(res, make_(FIXNUM, 1));
  set_cdr(res, res);
  push_root(res);
  gc();
  res = pop_root();
  assert(eq(car(res), make_(FIXNUM, 1)));
  assert(eq(cdr(res), res));

  res = make_pair();
  set_car(res, res);
  set_cdr(res, res);
  push_root(res);
  gc();
  res = pop_root();
  assert(eq(car(res), res));
  assert(eq(cdr(res), res));

  s = "(define #t (quote #t))";
  res = read_sexp(s);
  res = eval(res, peek_root());
  r = sexp_to_str(res);
  printf("%s\n", r);

  s = "(define #f (quote #f))";
  res = read_sexp(s);
  res = eval(res, peek_root());
  r = sexp_to_str(res);
  printf("%s\n", r);
  
  s = "(quote ())";
  res = read_sexp(s);
  res = eval(res, peek_root());
  r = sexp_to_str(res);
  printf("%s\n", r);
  assert(strcmp(r, "()") == 0);
  free(r);
  
  s = "1.234";
  res = read_sexp(s);
  res = eval(res, peek_root());
  r = sexp_to_str(res);
  printf("%s\n", r);
  assert(strcmp(r, "1.234000") == 0);
  free(r);

  s = "1234";
  res = read_sexp(s);
  res = eval(res, peek_root());
  r = sexp_to_str(res);
  printf("%s\n", r);
  assert(strcmp(r, "1234") == 0);
  free(r);
  
  s = "(add 1 2)";
  res = read_sexp(s);
  res = eval(res, peek_root());  
  r = sexp_to_str(res);
  printf("%s\n", r);
  assert(strcmp(r, "3") == 0);
  free(r);

  s = "((lambda (x y) (add x y)) 1 2)";
  res = read_sexp(s);
  printf("%s -> ", sexp_to_str(res));
  res = eval(res, peek_root());  
  r = sexp_to_str(res);
  printf("%s\n", r);
  assert(strcmp(r, "3") == 0);
  free(r);

  s = "(cons 1 2)";
  res = read_sexp(s);
  printf("%s -> ", sexp_to_str(res));
  res = eval(res, peek_root());  
  r = sexp_to_str(res);
  printf("%s\n", r);
  assert(strcmp(r, "(1 . 2)") == 0);
  free(r);

  
  s = "(set! x 1)";
  res = read_sexp(s);
  printf("%s -> ", sexp_to_str(res));
  res = eval(res, peek_root());
  r = sexp_to_str(res);
  printf("%s\n", r);
  assert(eq(res, var_not_found));
  free(r);

  s = "x";
  res = read_sexp(s);
  printf("%s -> ", sexp_to_str(res));
  res = eval(res, peek_root());  
  r = sexp_to_str(res);
  printf("%s\n", r);
  assert(eq(res, var_not_found));
  free(r);


  s = "(if (quote ()) 1 2)";
  res = read_sexp(s);
  printf("%s -> ", sexp_to_str(res));
  res = eval(res, peek_root());  
  r = sexp_to_str(res);
  printf("%s\n", r);
  assert(eq(res, make_(FIXNUM, 1)));
  free(r);

  s = "(if #t (add 3 1) 2)";
  res = read_sexp(s);
  printf("%s -> ", sexp_to_str(res));
  res = eval(res, peek_root());  
  r = sexp_to_str(res);
  printf("%s\n", r);
  assert(eq(res, make_(FIXNUM, 4)));
  free(r);

  s = "(define x 1)";
  res = read_sexp(s);
  printf("%s -> ", sexp_to_str(res));
  res = eval(res, peek_root());
  r = sexp_to_str(res);
  printf("%s\n", r);
  assert(eq(res, make_(FIXNUM, 1)));
  free(r);
  
  s = "(set! x 123)";
  res = read_sexp(s);
  printf("%s -> ", sexp_to_str(res));
  res = eval(res, peek_root());
  r = sexp_to_str(res);
  printf("%s\n", r);
  assert(eq(res, make_(FIXNUM, 123)));
  free(r);

  s = "x";
  res = read_sexp(s);
  printf("%s -> ", sexp_to_str(res));
  res = eval(res, peek_root());  
  r = sexp_to_str(res);
  printf("%s\n", r);
  assert(eq(res, make_(FIXNUM, 123)));
  free(r);

  res = make_pair();
  set_car(res, make_(FIXNUM, 1));
  set_cdr(res, res);
  push_root(res);
  gc();
  res = pop_root();
  r = sexp_to_str(res);
  printf("%s\n", r);
  assert(strcmp("(1 ...)", r) == 0);
  free(r);

  s = "(define x (lambda (x) x))";
  res = read_sexp(s);
  printf("%s -> ", sexp_to_str(res));
  res = eval(res, peek_root());  
  r = sexp_to_str(res);
  printf("%s\n", r);
  free(r);
}
