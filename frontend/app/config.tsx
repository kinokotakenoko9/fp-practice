const macros = `0 = \\f. \\x. x
1 = \\f. \\x. f x
2 = \\f. \\x. f (f x)
3 = \\f. \\x. f (f (f x))
6 = \\f. \\x. f (f (f (f (f (f x)))))

TRUE = \\a. \\b. a
FALSE = \\a. \\b. b
COND = \\i. \\t. \\e. i t e
ISZERO = \\f. f (\\x. FALSE) TRUE

PAIR = \\x. \\y. \\c. c x y
FST = \\p. p TRUE
SND = \\p. p FALSE
SWAP = \\p. PAIR (SND p) (FST p)

ADD = \\m. \\n. \\f. \\x. n f (m f x)
SUCC = \\n. \\f. \\x. f (n f x)
MUL = \\m. \\n. \\f. \\x. m (n f) x
PRED = \\n. \\f. \\x. n (\\g. \\h. h (g f)) (\\u. x) (\\u. u)

Y = \\f. (\\x. f (x x)) (\\x. f (x x))
Z = \\f. (\\x. f (\\v. x x v)) (\\x. f (\\v. x x v))
T = (\\x. \\y. y (x x y)) (\\x. \\y. y (x x y))

FACT_BODY = (\\fact. \\n. COND (ISZERO n) 1 (MUL n (fact (PRED n))))
FACT_Y = Y FACT_BODY
FACT_Z = Z FACT_BODY
FACT_T = T FACT_BODY
FACT = (\\fact. \\n. SND (n fact (PAIR n 1))) (\\p. PAIR (PRED (FST p)) (MUL (SND p) (FST p)))

FIB = (\\fib. \\n. SND (n fib (PAIR 1 0))) (\\p. PAIR (ADD (FST p) (SND p)) (FST p))

ADD 1 1 
`;

export default macros;
