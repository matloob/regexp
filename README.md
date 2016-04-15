# go regexp + RE2 DFA port

`import "matloob.io/regexp"`

See [golang.org/cl/12081](https://golang.org/cl/12081)

* The regexp conformance tests pass, but there's still work to be done on state cache management, thread-safety, and readability.
* Please don't use this in production.
