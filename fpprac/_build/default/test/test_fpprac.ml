open Lam

let%expect_test "parse var normal" =
  run_lambda "(x)";
  [%expect {|x|}]
;;

let%expect_test "parse var ws" =
  run_lambda "  (  x  )  ";
  [%expect {|x|}]
;;

let%expect_test "parse app normal" =
  run_lambda "x y";
  [%expect {|(x y)|}]
;;

let%expect_test "parse app ws" =
  run_lambda "  x   y  ";
  [%expect {|(x y)|}]
;;

let%expect_test "parse app manypar" =
  run_lambda "(((x y)))";
  [%expect {|(x y)|}]
;;

let%expect_test "parse app manypar ws" =
  run_lambda "  (  (  (  x   y  )  ) )  ";
  [%expect {|(x y)|}]
;;

let%expect_test "parse abs normal" =
  run_lambda "\\x.x";
  [%expect {|(λx. x)|}]
;;

let%expect_test "parse abs ws" =
  run_lambda "  \\  x  .  x  ";
  [%expect {|(λx. x)|}]
;;

let%expect_test "parse all" =
  run_lambda "(\\x. \\y. y (y x)) (\\z . z) w";
  [%expect {|(((λx. (λy. (y (y x)))) (λz. z)) w)|}]
;;
