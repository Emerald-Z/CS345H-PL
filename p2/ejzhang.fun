var x = 0
var testShadowing = 1
if testShadowing {
    print testShadowing
    testShadowing = testShadowing + 1
    var testShadowing = 100000
} else {
    print 1
    testShadowing = testShadowing + 1
    print testShadowing
}

if testShadowing var testShadowing = 1000000 else print -1
print testShadowing

{}

fun add(a, b) {
    a+b
}

var basicFunction = add(1, 2)
print basicFunction

fun f() {
    print 4
}

f ()

var runTryUntilError = 0
try {
    print 2000000
    runTryUntilError = runTryUntilError + 10
    x = x + 6
    print runTryUntilError
    var shouldNotPrint = 1000000
    print shouldNotPrint
} catch {
    print 5
}

var outsideWhileScope = 7
while x {
    print x
    outsideWhileScope = outsideWhileScope + 1
    x = x + - 1
}
print outsideWhileScope

fun multi(a, b, c) {
    print 1000000
    var x = a + b + c
    if x {
        print x
    } else {
        print 0
    }
}

fun funfun() {
    print multi(100, 200, 300)
}

print multi(10, 20, 30)

funfun()

{
    var funfun = 2
    try {
        print funfun
    } catch {
        var z = 10000 + 1
        print z
    }
}

