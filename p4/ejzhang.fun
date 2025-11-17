let basic1: int = 1
write basic1

let basic2: "hello" = "hello"
write basic2

let basic3: true = true
write basic3

let literalSum1: "a" | "b" = "b"
write literalSum1

let literalSum2: true | 0 = 0
write literalSum2

let literalSum3: bool | 42 | "hello" = 42
write literalSum3

fun basicFunction(a: int, b: int) a + b
var basicFunctionResult = call basicFunction(1, 2)
write basicFunctionResult

fun polyBasicFunction(a, b) a + b
var polyBasicFunctionResult = call polyBasicFunction(1, 2)
write polyBasicFunctionResult

fun literalBasicFunction(a: 3 | 4, b: 1 | 2) a + b
var literalBasicFunctionResult = call literalBasicFunction(3, 1)
write literalBasicFunctionResult
var literalBasicFunctionResult2 = call literalBasicFunction(4, 2)
write literalBasicFunctionResult2

fun typeCheckFunParams(p) {
    let result = call p(1, 2)
    write result
}
