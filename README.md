### lisp-vm-nim
This is a compiled, stack-machine-based Lisp virtual machine (VM) that is completely broken implemented in Nim. Single-file implementation. Created for learning purposes.
### Nim version
```
$ nim --version
Nim Compiler Version 2.2.12
```
### Run (REPL)
```
$ nim r main.nim -r

>> (define repeat (lambda (f) (lambda (x) (f (f x)))))
<closure>
>> ((repeat twice) 10)
40
```
### Read a file
```
$ nim r main.nim demo.lisp

"Hello, Lisp"
28.26
10
40
160
2560
655360
```
