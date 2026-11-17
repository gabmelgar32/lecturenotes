// #Sireum #Logika
//@Logika: --manual

import org.sireum._
import org.sireum.justification._
import org.sireum.justification.natded.prop._


//YOU DO THIS:
//Add proof blocks so the assert holds.

//Do not change anything in the program or assert.

val x: Z = Z.read()

assume (x >= 1 & x <= 3)

var result: Z = x

Deduce(
    1 ( x >= 1 & x <= 3 ) by Premise,
    2 ( result == x ) by Premise,
    3 ( x >= 1 ) by AndE1(1),
    4 ( x <= 3 ) by AndE2(1),
    5 ( result >= 1 ) by Algebra*(2, 3),
    6 ( result <= 3) by Algebra*(2, 4)
)

if (x == 1) {
    result = result * 6

    Deduce(
        1 ( Old(result) == x ) by Premise,
        2 ( x == 1 ) by Premise,
        3 ( Old(result) == 1 ) by Algebra*(1, 2),
        4 ( result == Old(result) * 6 ) by Premise,
        5 ( result == 6 ) by Algebra*(3, 4)
    )
} else {
    if (x == 2) {
        result = result * 3

        Deduce(
            1 ( Old(result) == x ) by Premise,
            2 ( x == 2 ) by Premise,
            3 ( Old(result) == 2 ) by Algebra*(1, 2),
            4 ( result == Old(result) * 3 ) by Premise,
            5 ( result == 6 ) by Algebra*(3, 4)
        )
    } else {
        result = result + 3

        Deduce(
            1 ( !(x == 1) ) by Premise,
            2 ( !(x == 2) ) by Premise,
            3 ( x >= 1 ) by Premise,
            4 ( x <= 3 ) by Premise,
            5 ( x == 3 ) by Algebra*(1,2,3,4),
            6 ( Old(result) == x ) by Premise,
            7 ( result == Old(result) + 3) by Premise,
            8 ( result == 6 ) by Algebra*(5, 6, 7)
        )
    }

    //add a Deduce block here to summarize what you learned in the inner if/else
    Deduce(
        1 ( result == 6 ) by Premise
    )
}

//add a Deduce block here to summarize what you learned in the outer if/else
Deduce(
    1 ( result == 6 ) by Premise
)


assert(result == 6)