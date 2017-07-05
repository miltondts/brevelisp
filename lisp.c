#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <errno.h>
#include <string.h>
#include <ctype.h>
#include <execinfo.h>

/* UTILS */

bool print_trace (void) {
  void *array[10];
  size_t size;
  char **strings;
  size_t i;

  size = backtrace (array, 10);
  strings = backtrace_symbols (array, size);

  printf ("Obtained %zd stack frames.\n", size);

  for (i = 0; i < size; i++)
     printf ("%s\n", strings[i]);

  free (strings);
  return true;
}

void assert(bool r) {
  if(!r) {
    print_trace();
    abort();
  }
}

typedef struct vector_t {
  void **elements;
  uint64_t size;
  uint64_t used;
} vector_t;

vector_t* make_vector(uint64_t size) {
  vector_t *vector = (vector_t*)malloc(sizeof(vector_t));
  vector->size = size;
  vector->used = 0;
  vector->elements = (void**)malloc(sizeof(void*)*vector->size);
  return vector;
}

void free_vector(vector_t *vector) {
  uint64_t i;
  for(i = 0; i<vector->used; i++){
    free(vector->elements[i]);
  }
  free(vector->elements);
  free(vector);
}

uint64_t insert(vector_t *vector, void *element) {
  if (vector->used >= vector->size) {
    vector->size++;
    vector->size *= 1.25;
    vector->elements = (void**)realloc(vector->elements, vector->size * sizeof(void*));
  }
  vector->elements[vector->used] = element;
  return vector->used++; 
}

char* result_cat(char **res) {
  int size = snprintf(NULL, 0, "%s%s%s%s%s", res[0], res[1], res[2], res[3], res[4]);
  char *s = calloc(size+1, sizeof(char));
  size = snprintf(s, size+1, "%s%s%s%s%s", res[0], res[1], res[2], res[3], res[4]);
  return s;
}

/* RUNTIME */

typedef union {
  uint64_t i;
  double f;
} typed_pointer;

const typed_pointer TYPE_MASK  = {.i = 0xFFFF000000000000};
const typed_pointer VALUE_MASK = {.i = 0x0000FFFFFFFFFFFF};
const typed_pointer FIXNUM     = {.i = 0xFFF1000000000000};
const typed_pointer SYMBOL     = {.i = 0xFFF2000000000000};
const typed_pointer PAIR       = {.i = 0xFFF3000000000000};
const typed_pointer PRIMITIVE  = {.i = 0xFFF4000000000000};

typed_pointer make_(typed_pointer type, uint64_t val) {
  typed_pointer res = {.i = type.i | (VALUE_MASK.i & val)};
  return res;
}

bool is_float(typed_pointer tp) {
  return !isnan(tp.f);
}

bool is_(typed_pointer type, typed_pointer tp) {
  return (tp.i & TYPE_MASK.i) == type.i;
}

bool eq(typed_pointer t1, typed_pointer t2) {
  return t1.i == t2.i;
}

typedef struct heap_t {
  typed_pointer *elements;
  typed_pointer *old_elements;
  uint64_t esize;
  uint64_t eused;
  typed_pointer *gc_roots;
  uint64_t rsize;
  uint64_t rused;
} heap_t;

heap_t* make_heap(uint64_t nelems, uint64_t nroots) {
  heap_t *h = (heap_t*)malloc(sizeof(heap_t));
  h->esize = nelems;
  h->eused = 0;
  h->elements = (typed_pointer*)malloc(sizeof(typed_pointer) * nelems);
  h->old_elements = (typed_pointer*)malloc(sizeof(typed_pointer) * nelems);
  h->rsize = nroots;
  h->rused = 0;
  h->gc_roots = (typed_pointer*)malloc(sizeof(typed_pointer) * nroots);
  return h;
}

void free_heap(heap_t *heap) {
  free(heap->elements);
  free(heap->old_elements);
  free(heap->gc_roots);
  free(heap);
}

vector_t *symbols;
heap_t *heap;
typed_pointer broken_heart, var_not_found, op_not_found,
  empty_list, false_symbol, true_symbol, lambda_symbol, set_symbol,
  define_symbol, if_symbol, procedure_symbol, quote_symbol,
  primitive_cons, primitive_add, primitive_eq, primitive_sub, primitive_mult;

typed_pointer insert_symbol(char *symbol) {
  for(uint64_t i = 0; i < symbols->used; i++){
    if(strcmp(symbol, symbols->elements[i]) == 0){
      return make_(SYMBOL, i);
    }
  }
  char *s = calloc(strlen(symbol)+1, sizeof(char));
  strcpy(s, symbol);
  return make_(SYMBOL, insert(symbols, s));
}

typed_pointer read_atom(char *token) {
  char *end = "";
  typed_pointer res;
  errno = 0;
  res = make_(FIXNUM, strtoll(token, &end, 0));
  if (strlen(end) > 0 || errno == ERANGE) {
    errno = 0;
    res.f = strtod(token, &end);
    if((strlen(end) > 0 || errno == ERANGE)) {
      return insert_symbol(token);
    }
  }
  return res;
}

uint64_t atom_end(char* s, uint64_t start) {
  uint64_t end = start + 1;
  while(!isspace(s[end]) && s[end] != '\0' && s[end] != '(' && s[end] != ')') {
    end++;
  }
  return end;
}

typed_pointer make_pair() {
  assert(heap->eused+2 < heap->esize);
  heap->eused++;
  return make_(PAIR, heap->eused++);
}

typed_pointer car(typed_pointer p) {
  assert(is_(PAIR, p));
  return heap->elements[p.i & VALUE_MASK.i];
}

void set_car(typed_pointer pair, typed_pointer e) {
  assert(is_(PAIR, pair));
  heap->elements[(int32_t)pair.i] = e;
}

void set_car_old(typed_pointer pair, typed_pointer e) {
  assert(is_(PAIR, pair));
  heap->old_elements[(int32_t)pair.i] = e;
}

typed_pointer cdr(typed_pointer p) {
  assert(is_(PAIR, p));
  return heap->elements[(p.i & VALUE_MASK.i) - 1];
}

void set_cdr(typed_pointer pair, typed_pointer e) {
  assert(is_(PAIR, pair));
  heap->elements[(int32_t)pair.i - 1] = e;
}

void set_cdr_old(typed_pointer pair, typed_pointer e) {
  assert(is_(PAIR, pair));
  heap->old_elements[(int32_t)pair.i - 1] = e;
}

typed_pointer car_old(typed_pointer p) {
  assert(is_(PAIR, p));
  return heap->old_elements[p.i & VALUE_MASK.i];
}

typed_pointer cdr_old(typed_pointer p) {
  assert(is_(PAIR, p));
  return heap->old_elements[(p.i & VALUE_MASK.i) - 1];
}

typed_pointer rellocate_pair(typed_pointer p) {
  typed_pointer old_car=car_old(p), old_cdr=cdr_old(p),
    new_pair, tmp;
  if(eq(broken_heart, old_car)) {
    return old_cdr;
  }
  uint64_t scan = heap->eused;
  new_pair = make_pair();
    
  set_car(new_pair, old_car);
  set_cdr(new_pair, old_cdr);

  set_car_old(p, broken_heart);
  set_cdr_old(p, new_pair);
  
  while(scan < heap->eused) {
    if(is_(PAIR, heap->elements[scan])) {
      if(eq(broken_heart, car_old(heap->elements[scan]))) {
	heap->elements[scan] = cdr_old(heap->elements[scan]);
      } else {
	// copy old pair
	tmp = make_pair();
	set_car(tmp, car_old(heap->elements[scan]));
	set_cdr(tmp, cdr_old(heap->elements[scan]));

	//set redirect address
	set_car_old(heap->elements[scan], broken_heart);
	set_cdr_old(heap->elements[scan], tmp);
	
	heap->elements[scan] = tmp;
      }
    }
    scan++;
  }
    
  return new_pair;
}

typed_pointer rellocate_root(typed_pointer root) {
  if(is_(PAIR, root)) {
    return rellocate_pair(root);
  } else {
    return root;
  }
}

void gc() {
  typed_pointer *tmp;
  tmp = heap->elements;
  heap->elements = heap->old_elements;
  heap->old_elements = tmp;
  heap->eused = 0;
  
  for(int i = 0; i < heap->rused; i++){
    heap->gc_roots[i] = rellocate_root(heap->gc_roots[i]);
  }
}

void push_root(typed_pointer root) {
  assert(heap->rused+1 < heap->rsize);
  heap->gc_roots[heap->rused++] = root; 
}

typed_pointer pop_root() {
  assert(heap->rused-1 >= 0 && heap->rused-1 < heap->rsize);
  return heap->gc_roots[--(heap->rused)];
}

typed_pointer peek_root() {
  return heap->gc_roots[heap->rused-1];
}

typed_pointer cons(typed_pointer tcar, typed_pointer tcdr) {
  push_root(tcar);
  push_root(tcdr);
  gc();
  tcdr = pop_root();
  tcar = pop_root();
  typed_pointer new_pair = make_pair();
  set_car(new_pair, tcar);
  set_cdr(new_pair, tcdr);
  return new_pair;
}

char* get_token(char **ps) {
  while(isspace(*ps[0])) {
    (*ps)++;
  }
  
  if(*ps[0] == '\0') {
    return NULL;
  } else if(*ps[0] == '(') {
    (*ps)++;
    char *token = calloc(2, sizeof(char));
    token[0] = '(';
    return token;
  } else if(*ps[0] == ')') {
    (*ps)++;
    char *token = calloc(2, sizeof(char));
    token[0] = ')';
    return token;
  } else {
    char *start = *ps;
    while(!isspace(*ps[0]) && *ps[0] != '\0' && *ps[0] != '(' && *ps[0] != ')') {
      (*ps)++;
    }
    char *token = calloc(*ps - start + 1, sizeof(char));
    memcpy(token, start, *ps - start);
    return token;
  }
}

typed_pointer read_list(char **s) {
  char *token = get_token(s);
  assert(token != NULL);
  typed_pointer res;
  if(strcmp(token, ")") == 0) {
    res = empty_list;
  } else if(strcmp(token, "(") == 0) {
    typed_pointer t1 = read_list(s);
    push_root(t1);
    typed_pointer t2 = read_list(s);
    res = cons(pop_root(), t2);
  } else {
    res = cons(read_atom(token), read_list(s));
  }
  free(token);
  return res;
}

typed_pointer read_sexp(char *s) {
  char *token = get_token(&s);
  assert(token != NULL && strcmp(token, ")") != 0);
  typed_pointer res;
  if(strcmp(token, "(") == 0) {
    res = read_list(&s);
  } else {
    res = read_atom(token);
  }
  free(token);
  return res;
}

char* atom_to_str(typed_pointer atom) {
  char *res;
  int size;
  if(is_(FIXNUM, atom)) {
    size = snprintf(NULL, 0, "%d", (int32_t)atom.i);
    res = calloc(size+1, sizeof(char));
    size = snprintf(res, size+1, "%d", (int32_t)atom.i);
    return res;
  } else if(is_(SYMBOL, atom)){
    char *s = symbols->elements[atom.i & VALUE_MASK.i];
    char *res = calloc(strlen(s)+1, sizeof(char));
    strcpy(res, s);
    return res;
  } else if(is_(PRIMITIVE, atom)){
    size = snprintf(NULL, 0, "#PRIMITIVE#%d#", (int32_t)atom.i);
    res = calloc(size+1, sizeof(char));
    size = snprintf(res, size+1, "#PRIMITIVE#%d#", (int32_t)atom.i);
    return res;
  } else {
    size = snprintf(NULL, 0, "%f", atom.f);
    res = calloc(size+1, sizeof(char));
    size = snprintf(res, size+1, "%f", atom.f);
    return res;
  }
}

uint64_t pused = 0;
uint64_t psize = 1024;
typed_pointer parents[1024];

void push(typed_pointer p) {
  assert(pused < psize);
  parents[pused++] = p;
}

void pop() {
  pused--;
}

bool contains(typed_pointer p) {
  for(uint64_t i = 0; i < pused; i++) {
    if(eq(parents[i], p)) {
      return true;
    }
  }
  return false;
}

char* pair_to_str(typed_pointer pair) {
  char *res[5] = {"", "", "", "", ""};
  char *s;
  if(contains(pair)) {
    s = calloc(4, sizeof(char));
    s[0] = '.';
    s[1] = '.';
    s[2] = '.';
    s[3] = ')';
    return s;
  }
  
  if(is_(PAIR, car(pair))) {
    res[0] = "(";
    push(pair);
    res[1] = pair_to_str(car(pair));
    pop();
  } else {
    res[1] = atom_to_str(car(pair));
  }
 
  if(is_(PAIR, cdr(pair))) {
    res[2] = " ";
    push(pair);
    res[3] = pair_to_str(cdr(pair));
    pop();
    s = result_cat(res);
    free(res[3]);
  } else if(eq(cdr(pair), empty_list)) {
    res[2] = ")";
    s = result_cat(res);
  } else {
    res[2] = " . ";
    res[3] = atom_to_str(cdr(pair));
    res[4] = ")";
    s = result_cat(res);
    free(res[3]);
  }
  
  free(res[1]);
  return s;
}

char* sexp_to_str(typed_pointer sexp) {
  if(is_(PAIR, sexp)) {
    char *t = pair_to_str(sexp);
    char *res = calloc(strlen(t) + 2, sizeof(char));
    strcat(res, "(");
    strcat(res, t);
    free(t);
    return res;
  } else {
    return atom_to_str(sexp);
  }
}

/* EVAL */

bool is_self_evaluating(typed_pointer exp) {
  return !is_(PAIR, exp) && !is_(SYMBOL, exp);
}

bool is_variable(typed_pointer exp) {
  return is_(SYMBOL, exp) && !eq(exp, empty_list);
}

typed_pointer make_frame(typed_pointer vars, typed_pointer vals) {
  return cons(vars, vals);
}

typed_pointer frame_vars(typed_pointer frame) {
  return car(frame);
}

typed_pointer frame_vals(typed_pointer frame) {
  return cdr(frame);
}

typed_pointer first_frame(typed_pointer env) {
  return car(env);
}

typed_pointer enclosing_env(typed_pointer env) {
  return cdr(env);
}

typed_pointer scan(typed_pointer frame, typed_pointer var) {
  typed_pointer vars = frame_vars(frame), vals = frame_vals(frame);
  while(!eq(vars, empty_list)) {
    if(eq(car(vars), var)) {
      return car(vals);
    }
    vars = cdr(vars);
    vals = cdr(vals);
  }
  return var_not_found;
}

typed_pointer lookup_variable_value(typed_pointer var, typed_pointer env) {
  typed_pointer frame, val = var_not_found;
  while(!eq(env, empty_list)) {
    frame = first_frame(env);
    val = scan(frame, var);
    if (!eq(val, var_not_found)) {
      return val;
    }
    env = enclosing_env(env);
  }
  return val;
}

bool is_quoted(typed_pointer exp) {
  return eq(car(exp), quote_symbol);
}

typed_pointer text_of_quotation(typed_pointer exp) {
  return car(cdr(exp));
}

bool is_assignment(typed_pointer exp) {
  return eq(car(exp), set_symbol);
}

typed_pointer assignment_var(typed_pointer exp) {
  return car(cdr(exp));
}

typed_pointer assignment_val(typed_pointer exp) {
  return car(cdr(cdr(exp)));
}

typed_pointer set_in_frame(typed_pointer frame, typed_pointer var, typed_pointer val) {
  typed_pointer vars = frame_vars(frame), vals = frame_vals(frame);
  while(!eq(vars, empty_list)) {
    if(eq(car(vars), var)) {
      set_car(vals, val);
      return car(vals);
    }
    vars = cdr(vars);
    vals = cdr(vals);
  }
  return var_not_found;
}

typed_pointer set_var_val(typed_pointer var, typed_pointer val, typed_pointer env) {
  typed_pointer frame, old_val;
  while(!eq(env, empty_list)) {
    frame = first_frame(env);
    old_val = set_in_frame(frame, var, val);
    if (!eq(old_val, var_not_found)) {
      return val;
    }
    env = enclosing_env(env);
  }
  
  return var_not_found;
}

bool is_definition(typed_pointer exp) {
  return eq(car(exp), define_symbol);
}

typed_pointer def_var(typed_pointer exp) {
  if(is_(SYMBOL, car(cdr(exp)))) {
    return car(cdr(exp));
  } else {
    return car(car(cdr(exp)));
  }
}

typed_pointer make_lambda(typed_pointer formals, typed_pointer body) {
  return cons(lambda_symbol, cons(formals, body));
}

bool is_lambda(typed_pointer exp) {
  return eq(car(exp), lambda_symbol);
}

typed_pointer lambda_parameters(typed_pointer exp) {
  return car(cdr(exp));
}

typed_pointer lambda_body(typed_pointer exp) {
  return cdr(cdr(exp));
}

typed_pointer def_val(typed_pointer exp) {
  if(is_(SYMBOL, car(cdr(exp)))) {
    return car(cdr(cdr(exp)));
  } else {
    return make_lambda(cdr(car(cdr(exp))), cdr(cdr(exp)));
  }
}

typed_pointer define_var(typed_pointer var, typed_pointer val, typed_pointer env) {
  typed_pointer frame = first_frame(env);
  typed_pointer r = set_in_frame(frame, var, val);
  if(eq(r, var_not_found)) {
    push_root(val);
    push_root(frame);
    
    typed_pointer vals = cons(val, frame_vals(frame));
    frame = peek_root();
    set_cdr(frame, vals);
    // var is always an atom doesn't need to be saved
    
    typed_pointer vars = cons(var, frame_vars(frame));
    frame = pop_root();
    set_car(frame, vars);
    return pop_root();
  } else {
    return r;
  }
}

bool is_if(typed_pointer exp) {
  return eq(car(exp), if_symbol);
}

typed_pointer if_predicate(typed_pointer exp) {
  return car(cdr(exp));
}

typed_pointer if_consequent(typed_pointer exp) {
  return car(cdr(cdr(exp)));
}

typed_pointer if_alternative(typed_pointer exp) {
  return car(cdr(cdr(cdr(exp))));
}

bool is_application(typed_pointer exp) {
  return is_(PAIR, exp);
}

typed_pointer make_procedure(typed_pointer params, typed_pointer body, typed_pointer env) {
  push_root(params);
  push_root(body);
  typed_pointer acc = cons(env, empty_list);
  acc = cons(pop_root(), acc);
  acc = cons(pop_root(), acc);
  return cons(procedure_symbol, acc);
}

bool is_procedure(typed_pointer exp) {
  return is_(PAIR, exp) && eq(car(exp), procedure_symbol);
}

typed_pointer procedure_params(typed_pointer exp) {
  return car(cdr(exp));
}

typed_pointer procedure_body(typed_pointer exp) {
  return car(cdr(cdr(exp)));
}

typed_pointer procedure_env(typed_pointer exp) {
  return car(cdr(cdr(cdr(exp))));
}

typed_pointer operator(typed_pointer exp) {
  return car(exp);
}

typed_pointer operands(typed_pointer exp) {
  return cdr(exp);
}

bool has_operands(typed_pointer ops) {
  return !eq(ops, empty_list);
}

typed_pointer first_operand(typed_pointer ops) {
  return car(ops);
}

typed_pointer rest_operands(typed_pointer ops) {
  return cdr(ops);
}

typed_pointer eval(typed_pointer exp, typed_pointer env);

typed_pointer list_of_values(typed_pointer ops, typed_pointer env) {
  uint64_t i = 0;
  typed_pointer evaled;
  
  while(has_operands(ops)) {
    push_root(env);
    push_root(rest_operands(ops));
    evaled = eval(first_operand(ops), env);
    ops = pop_root();
    env = pop_root();
    push_root(evaled);
    i++;
  }

  typed_pointer res = empty_list;
  while(i-- > 0) {
    res = cons(pop_root(), res);
  }
  return res;
}

typed_pointer extend_env(typed_pointer vars, typed_pointer vals, typed_pointer base_env) {
  push_root(base_env);
  typed_pointer frame = make_frame(vars, vals);
  base_env = pop_root();
  return cons(frame, base_env);
}

typed_pointer eval_sequence(typed_pointer exps, typed_pointer env) {
  while(!eq(cdr(exps), empty_list)) {
    push_root(env);
    push_root(cdr(exps));
    eval(car(exps), env);
    exps = pop_root();
    env = pop_root();
  }
  return eval(car(exps), env);
}

typed_pointer compound_apply(typed_pointer op_val, typed_pointer ops_vals) {
  push_root(procedure_body(op_val));
  typed_pointer env = extend_env(procedure_params(op_val),
                                 ops_vals,
                                 procedure_env(op_val));
  return eval_sequence(pop_root(), env);
}

typed_pointer primitive_apply(typed_pointer op_val, typed_pointer ops_vals) {
  if(eq(op_val, primitive_cons)) {
    return cons(car(ops_vals), car(cdr(ops_vals)));
  } else if(eq(op_val, primitive_add)) {
    return make_(FIXNUM,
		 (unsigned int)((int)(car(ops_vals).i) +
				(int)(car(cdr((ops_vals))).i)));
  } else if(eq(op_val, primitive_sub)) {
    return make_(FIXNUM,
		 (unsigned int)((int)(car(ops_vals).i) -
				(int)(car(cdr((ops_vals))).i)));
  } else if(eq(op_val, primitive_mult)) {
    return make_(FIXNUM,
		 (unsigned int)((int)(car(ops_vals).i) *
				(int)(car(cdr((ops_vals))).i)));
  } else if(eq(op_val, primitive_eq)) {
    if(eq(car(ops_vals), car(cdr((ops_vals))))) {
      return true_symbol;
    } else {
      return false_symbol;
    }
  }
  return op_not_found;
}

typed_pointer apply(typed_pointer op_val,  typed_pointer ops_vals) {
  if(is_procedure(op_val)) {
    return compound_apply(op_val, ops_vals);
  } else {
    return primitive_apply(op_val, ops_vals);
  }
}

typed_pointer eval(typed_pointer exp, typed_pointer env) {
  if(is_self_evaluating(exp)) {
    return exp;
  } else if(is_variable(exp)) {
    return lookup_variable_value(exp, env);
  } else if (is_quoted(exp)) {
    return text_of_quotation(exp);
  } else if (is_assignment(exp)) {
    return set_var_val(assignment_var(exp), assignment_val(exp), env);
  } else if (is_definition(exp)) {
    push_root(exp);
    push_root(env);
    typed_pointer dval = def_val(exp);
    typed_pointer val  = eval(dval, peek_root());
    env = pop_root();
    exp = pop_root();
    return define_var(def_var(exp), val, env);
  } else if (is_if(exp)) {
    push_root(exp);
    push_root(env);
    typed_pointer pred_val = eval(if_predicate(exp), env);
    env = pop_root();
    exp = pop_root();
    if(eq(pred_val, false_symbol)) {
      return eval(if_alternative(exp), env);
    } else {
      return eval(if_consequent(exp), env);
    }
  } else if (is_lambda(exp)) {
    return make_procedure(lambda_parameters(exp), lambda_body(exp), env);
  } else {
    assert(is_application(exp));
    typed_pointer ops = operands(exp);
    push_root(env);
    push_root(ops);
    typed_pointer op_val = eval(operator(exp), env);
    ops = pop_root();
    env = pop_root();
    push_root(op_val);
    typed_pointer ops_vals = list_of_values(ops, env);
    op_val = pop_root();
    return apply(op_val, ops_vals);
  }
}

void setup_env() {
  empty_list = insert_symbol("()");
  quote_symbol = insert_symbol("quote");
  set_symbol = insert_symbol("set!");
  define_symbol = insert_symbol("define");
  if_symbol = insert_symbol("if");
  lambda_symbol = insert_symbol("lambda");
  true_symbol = insert_symbol("#t");
  false_symbol = insert_symbol("#f");
  broken_heart = insert_symbol("#BROKEN-HEART#");
  var_not_found = insert_symbol("#VAR-NOT-FOUND#");
  op_not_found = insert_symbol("#OP-NOT-FOUND#");
  procedure_symbol = insert_symbol("#PROCEDURE#");

  primitive_cons = make_(PRIMITIVE, 0);
  primitive_add = make_(PRIMITIVE, 1);
  primitive_sub = make_(PRIMITIVE, 2);
  primitive_mult = make_(PRIMITIVE, 3);
  primitive_eq = make_(PRIMITIVE, 4);

  typed_pointer primitive_proc_names = read_sexp("(eq? mult sub cons add)");
  push_root(primitive_proc_names);
  typed_pointer primitive_proc_objects =
    cons(primitive_eq,
	 cons(primitive_mult,
	      cons(primitive_sub,
		   cons(primitive_cons,
			cons(primitive_add, empty_list)))));
  primitive_proc_names = pop_root();
  typed_pointer init_env = extend_env(primitive_proc_names,
                                      primitive_proc_objects,
                                      empty_list);
  push_root(init_env);
}

void repl(FILE *f) {
  char c;
  int64_t balance = 0;
  
  uint64_t ssize = 4096;
  uint64_t sused = 0;
  char s[ssize];

  printf("> ");
  while((c = getc(f)) != EOF) {
    while(isspace(c)) {
      c = getc(f);
    }

    while(!(isspace(c) && balance == 0)) {
      if(c == '('){
	balance++;
      }
      if(c == ')'){
	balance--;
      }
      assert(sused < ssize);
      s[sused++] = c;
      c = getc(f);
    }
    s[sused] = '\0';
    typed_pointer res = read_sexp(s);
    res = eval(res, peek_root());
    char *rs = sexp_to_str(res);
    printf("%s\n", rs);
    free(rs);
    sused = 0;
    printf("> ");
  }
}

int main(int argc, char** argv) {
  setvbuf(stdout, NULL, _IONBF, 0);

  symbols = make_vector(50);
  heap = make_heap(512, 64);

  setup_env();
  repl(stdin);
  
  free_vector(symbols);
  free_heap(heap);
  return 0;
}
