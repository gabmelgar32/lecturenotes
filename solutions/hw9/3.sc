// #Sireum #Logika
//@Logika: --manual
import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


//bOU DO THIS:
//Add deduce blocks so each assert holds.

//Do not change anbthing in the program or asserts.


var a: Z = Z.prompt("Enter a an integer between 5-10: ")
var b: Z = Z.prompt("Enter a an integer between 5-10: ")
var c: Z = Z.prompt("Enter a an integer between 5-10: ")

val aOrig: Z = a

assume(a >= 5)
assume(a <= 10)
assume(b >= 5)
assume(b <= 10)
assume(c >= 5)
assume(c <= 10)

a = a + b

Deduce(
    1 ( Old(a) >= 5 ) by Premise,
    2 ( Old(a) <= 10 ) by Premise,
    3 ( b >= 5 ) by Premise,
    4 ( b <= 10 ) by Premise,

    5 ( aOrig == Old(a) ) by Premise,
    6 ( a == Old(a) + b) by Premise,
    7 ( a == aOrig + b ) by Algebra*(7,8),

    8 ( a >= 10 ) by Algebra*(1,3,8),
    9 ( a <= 20 ) by Algebra*(2,4,8),
    10 ( a >= 10 & a <= 20 ) by AndI(8, 9)
)

assert(a == aOrig + b)
assert(a >= 10 & a <= 20)


a = a + c

Deduce(
    1( a == Old(a) + c) by Premise,
    2 ( Old(a) == aOrig + b) by Premise,
    3 ( a == aOrig + b + c ) by Algebra*(1,2),

    4 ( c >= 5 ) by Premise,
    5 ( c <= 10 ) by Premise,
    6 ( Old(a) >= 10 ) by Premise,
    7 ( Old(a) <= 20 ) by Premise,

    8 ( a >= 15 ) by Algebra*(1, 5, 7),
    9 ( a <= 30 ) by Algebra*(1, 6, 8),
    10 ( a >= 15 & a <= 30 ) by AndI(8, 9)
)

assert(a == aOrig + b + c)
assert(a >= 15 & a <= 30)