// #Sireum #Logika
//@Logika: --manual
import org.sireum._
import org.sireum.justification._


//YOU DO THIS:
//Add deduce blocks so both asserts hold

//You should use the Subst rule at least twice in your deduce blocks.

//Do not change anything in the program or asserts.


var num: Z = Z.prompt("Enter a number: ")
val numOrig: Z = num

num = num + num

Deduce(
    1 ( numOrig == Old(num) )   by Premise,
    2 ( num == Old(num) + Old(num) )  by Premise,
    3 ( num == numOrig + numOrig ) by Subst_>(1,2),
    4 ( num == 2*numOrig ) by Algebra*(3)
)

assert(num == 2*numOrig)

num = 2*num + 1

Deduce(
    1 ( num == 2*Old(num) + 1 ) by Premise,
    2 ( Old(num) == 2*numOrig ) by Premise,
    3 ( num == 2*(2*numOrig) + 1 ) by Subst_<(2, 1),
    4 ( num == 4*numOrig +1   ) by Algebra*(3)  
)


assert(num == 4*numOrig + 1)