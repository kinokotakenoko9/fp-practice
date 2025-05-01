open Lam
open Js_of_ocaml

let _ =
  Js.export_all
    (object%js
       method get_ao_trace s n svi sdr smp =
         get_lambda__small_step AO s n svi sdr smp

       method get_no_trace s n svi sdr smp =
         get_lambda__small_step NO s n svi sdr smp

       method get_cbn_trace s n svi sdr smp =
         get_lambda__small_step CBN s n svi sdr smp

       method get_cbv_trace s n svi sdr smp =
         get_lambda__small_step CBV s n svi sdr smp
    end)
