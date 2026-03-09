# Some examples

## type definitions 

All types, constructors, and record names must begin with an uppercase character. 

> perhaps it would be worth having sugar for a type with a single constructor (that has the same name as the type): this is a common pattern. 

### A non parameterised algebraic type 
constructors implicitly have the same type and do not need explicit types.  
```
type TrafficLight {
    constructor Red; 
    constructor Yellow; 
    constructor Green;
}
```

> perhaps something like `type TrafficLight = Red | Yellow | Green;` would be better sugar but im not too sure about introducing radically different notation. 

### A vector 
```
type Vect<Ty t>(Nat n) {
    constructor Nil() of Vect<t>(0);
    constructor Cons(t head, Vect(n, t) tail) of Vect<t>(1+n);
}
```
> "<>" is for implicit arguments. Perhaps the distinction between implicit and explicit arguments is not as important in imperative programming as it is in dependently typed programming, and this can be an additional burden: however, this is how types are parameterised in java/cpp (separately from arguments) and hence i think it's not too much of a stretch. 

## record definitions 

> in traditional dependently typed programming, a record also comes equipped with an explicit constructor. I've abstracted that away into an implicit record constructor that has the same name as the record itself. I'm not sure if that's an abstraction that can cause problems with comprehension of types and terms. 

### A simple student record

```
record Student {
    String name; 
    Nat age;     
}
```

### A dependent pair as a record
```
record DPairRec(Ty t, Func(t a => Ty) p) {
    t fst; 
    p(fst) snd;
}
```
> perhaps the => in the function type should be a ->
## function definitions

a minimal function definition looks like `func name() { ;; }`. 

function definitions may also contain effects (`[IO]`), arguments (in `<>` or `()` if implicit or explicit, respectively), and a return type (`func name() returns Nat`). No explicit return type means the function returns `()`. Function bodies are contained in `{}` and must be one or more statements. 

Effectful (`[IO]`) functions are translated into an idris do block automatically. all io functions must be prepended by `IO.`. 
### hello world 

```
[IO] func main() {
    IO.putStr("hello, world!\n");
}
```

### IO and assignment
```
[IO] func ioAppend(String x) returns String {
    IO.putStr("gimme a string");
    String y = IO.getLine(); 
    return (x ++ y);
}
```
### Loops and scoping 
```
func testLoop (Nat n) returns Nat {
    Nat x = 11;
    x = 12; 
    if (x < 10) {
        while (n < 10) {
            x = x + 1;
            n = n + 4;
        }
        n = n + 1;
    }
    else {
        n = n + 2; 
    }
    return n; 
}
```
> any statements after branching conditionals will be elaborated explicitly into all branches. 
### nested loops 
```
func testNestedLoops (Nat n) returns Nat {
    Nat x = 11; 
    while (n < x) {
        n = n + 1; 
        n = n + 3;
        Nat m = n;
        while (m < x) {
            m = m + 1;
        }
    }
    return n;
}
```
> each loop will create its own recursive helper and scoping will be as expected.

### switch statements 

```
func nextLight(TrafficLight t) returns TrafficLight { 
    switch(t) {
        case (Red) { 
            return Yellow;
        }
        case (Yellow) {
            return Green; 
        }
        case (Green) {
            return Red;
        }
    }
}
```

> will be elaborated into pattern matching 
> if all constructors are not split on a default case must be provided
> a default case is just the `_` case in idris
> scoping is the same as conditionals: any statements after the block will be replicated into each branch. 

### eif and ewhile 
```
func search (Nat n, Vect(n, Nat) ls, Nat x) returns Maybe(Fin(n)) {
    Nat i = 0;
    Maybe(Fin(n)) ret = Nothing; 
    ewhile(i < n) {
        eif ((index(natToFinLT(i), ls)) == x) {
            ret = Just((natToFinLT(i))); 
        }
        else {;;}
        i = 1 + i; 
    }
    return ret; 
}
```
> both eif and ewhile conditionals will be elaborated into a dependent pattern match


## FSM

The parts we talked about ideally improving were: the FSM signature, including where the resource and the stateType should be instantiated, and what the replacement (if any) for `impl FSM` should be; the attachment of the init and exec functions to the FSM itself. to detach the exec function, we would need some sort of identifier for the state machine instantiation to tie the two together. 

### minimal FSM 

this is a bit nonsensical but just shows each part of the FSM. 

``` 
impl FSM {
    resource = String s; 
    stateTy = Bool; 

    action len returns Nat n [True --> (n > 10) ? True : False];
    func len() returns Nat {
        return length(s);
    }
} with init func initStr(String s) {
    return s; 
} with exec [IO] func main(String s) [True] {
    Nat n = s.len();
    IO.print(n); 
}
```

> writing a minimal example actually reminded me that we should have some way to abstract over states as well: for example, if an action is valid in any state i should be able to quantify that. 

### Data store FSM

```
impl FSM {
    resource = Store st;
    stateTy = Access;

    action login returns LoginResult r [LoggedOut --> (r == OK) ? LoggedIn : LoggedOut];
    [IO] func login() returns LoginResult {
        IO.print("enter password");
        String pw = IO.getLine();
        if (pw == "password123") {
            return OK;
        } else {
            return BadPassword;
        }
    }

    action logout [LoggedIn --> LoggedOut];
    [IO] func logout() {
        IO.print("logging out");
    }

    action readSecret returns String [LoggedIn];
    [IO] func readSecret() returns String {
        return st.secret;
    }
} with init func initStore(String secret, String pub) returns Store {
        return Store(secret, pub);
    }
  with exec [IO] func main() [LoggedOut] {
    LoginResult res = st.login();
    if (res == OK) {
        String secret = st.readSecret(); 
        IO.print(secret);
        st.logout();
    } else {
        IO.print("bad password");
    }
}
```

> one other solution here is to have the states defined inline in the FSM. so states = [LoggedIn, LoggedOut] or something along those lines. but i think it's a worse solution personally because it abstracts away the idea of the state having an explicit type even if it can be transformed easily. 

## Other thoughts

> perhaps ite as a term should not use `{}` as this is typically for statements, however it seems confusing to introduce specific syntax for something so similar. Perhaps it should just be if (a) then (b) else (c) but the addition of `then` as a keyword here but not in the statement case is confusing. 