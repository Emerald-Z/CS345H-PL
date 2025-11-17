var x1: 3 = 1 + 2
write x1

var x2: int = 5
write x2

var x3: "hello" = "hello"
write x3

var x4: true = true
write x4

var y1: "a" | "b" = "b"
write y1

var y2: true | 0 = 0
write y2

var y3: bool | 42 = 42
write y3

var y4 = if true 10 else false
write y4

fun id(x) x
var p1 = call id(42)
write p1
var p2 = call id(true)
write p2
var p3 = call id("test")
write p3

fun const(x, y) x
var p4 = call const(10, true)
write p4
var p5 = call const("str", 99)
write p5

fun add(x: int, y: int) x + y
var f1 = call add(5, 10)
write f1

fun apply(f: fun(int) -> int, x: int) call f(x)
fun double(n: int) n * 2
var f2 = call apply(double, 21)
write f2

fun add3(a: int, b: int, c: int) a + b + c
var addpartial = call add3(1, 2)
write addpartial
var f3 = call addpartial(3)
write f3

var t1 = [1, true, "hello"]
write t1
var t2: 1 = t1[0]
write t2
var t3: true = t1[1]
write t3

var t4 = [[1, 2], [3, 4]]
write t4

fun square(n: int) n * n
var t5 = [42, square]
write t5

var d1 = #[]
let d1[0] = 100
let d1[1] = 200
write d1
var d2 = d1[0]
write d2
var d3 = d1[1]
write d3

var c1: int = (if true 1 else 2) * 5
write c1

var c2: int = 0
while c2 < 5 {
  let c2 = c2 + 1
}
write c2

var c3: int = 0
for i 0 5 {
  let c3 = c3 + i
}
write c3

var c4 = try 10 / 0 catch Any 0
write c4

var s1: bool = true
{
  var s1: int = 10
  var s2 = s1 + 5
  write s2
}
write s1 / 2

var s4: int = 5
write s4
fun shadow(s4: bool) s4
var s5 = call shadow(false)
write s5

var b1: 30 = 10 + 20
write b1
var b2: 2 = 5 - 3
write b2
var b3: 20 = 4 * 5
write b3
var b4: 5 = 20 / 4
write b4

var b5: "hello world" = "hello" + " world"
write b5
var b6: "xxx" = "x" * 3
write b6

var b7: bool = 10 < 20
write b7
var b8: bool = "a" < "b"
write b8

var m1: 5 = 5
write m1
var m2: int = m1 + 10
write m2
var m3: int = m2 * 2
write m3

fun compose(f, g, x) call f(call g(x))
fun inc(n: int) n + 1
var m5: int = call compose(double, inc, 10)
write m5

var e1 = []
write e1
