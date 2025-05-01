const macros = `0 = \\f. \\x. x
1 = \\f. \\x. f x
2 = \\f. \\x. f (f x)
3 = \\f. \\x. f (f (f x))
4 = \\f. \\x. f (f (f (f x)))
5 = \\f. \\x. f (f (f (f (f x))))
6 = \\f. \\x. f (f (f (f (f (f x)))))
7 = \\f. \\x. f (f (f (f (f (f (f x))))))
8 = \\f. \\x. f (f (f (f (f (f (f (f x)))))))
9 = \\f. \\x. f (f (f (f (f (f (f (f (f x))))))))
10 = \\f. \\x. f (f (f (f (f (f (f (f (f (f x)))))))))

TRUE = \\a. \\b. a
FALSE = \\a. \\b. b
AND = \\p. \\q. p q FALSE
OR = \\p. \\q. p TRUE q
NOT = \\p. p FALSE TRUE
IF = \\c. \\t. \\e. c t e

SUCC = \\n. \\f. \\x. f (n f x)
PRED = \\n. \\f. \\x. n (\\g. \\h. h (g f)) (\\u. x) (\\u. u)
ADD = \\m. \\n. \\f. \\x. m f (n f x)
SUB = \\m. \\n. n PRED m
MUL = \\m. \\n. \\f. m (n f)
POW = \\b. \\e. e b

IS_ZERO = \\n. n (\\x. FALSE) TRUE
IS_EVEN = \\n. (n NOT) TRUE
IS_ODD = \\n. (n NOT) FALSE
LEQ = \\m. \\n. IS_ZERO (SUB m n)

PAIR = \\x. \\y. \\p. p x y
FST = \\p. p TRUE
SND = \\p. p FALSE
SWAP = \\p. PAIR (SND p) (FST p)

Y = \\f. (\\x. f (x x)) (\\x. f (x x))
Z = \\f. (\\x. f (\\v. x x v)) (\\x. f (\\v. x x v))

I = \\x. x
S = \\x. \\y. \\z. x z (y z)
K = \\x. \\y. x

B = \\x. \\y. \\z. x (y z)
C = \\x. \\y. \\z. x z y
W = \\x. \\y. x y y

FACT_REC = Z (\\fact. \\n. IF (IS_ZERO n) 1 (MUL n (fact (PRED n))))
FACT = (\\fact. \\n. SND (n fact (PAIR n 1))) (\\p. PAIR (PRED (FST p)) (MUL (SND p) (FST p)))

FIB_REC = Z (\\fib. \\n. IF (IS_ZERO n) 0 (IF (IS_ZERO (PRED n)) 1 (ADD (fib (PRED n)) (fib (PRED (PRED n))))))
FIB = (\\fib. \\n. SND (n fib (PAIR 1 0))) (\\p. PAIR (ADD (FST p) (SND p)) (FST p))

CONS = \\h. \\t. PAIR h t
NIL = \\x. TRUE
HEAD = FST
TAIL = SND
IS_EMPTY = \\l. l (\\h. \\t. FALSE) 

ADD 1 1 

`;

export default macros;
