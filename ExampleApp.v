(* An example adapted from OKWS, a web server with privilege separation 
   Reference paper: 
   Maxwell Krohn, Building Secure High-Performance Web Services with OKWS *)

Require Import Arith Process Refinement ModelCheck.

Definition chs : channels := fun _ => nat.

Module okd.

  Definition policy (pr : process chs) : process chs := ##[(Recv, "80"), (Send, "80"), (Send, "svc1")], pr.

End okd.

Module svc1.
