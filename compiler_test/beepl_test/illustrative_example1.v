
(* struct Packet {
  src: int;
  dst: int;
}

external fun lookup_config(id: int): <read r> option *int
external fun log(msg: string): <total> unit

fun process_packet(): <alloc r, read r, write r, exn> unit {
  let pkt := ref Packet { src = 42, dst = 7 } in           // Non-null pointer
  let src := pkt.src in                                    // Read from ref

  let config_ptr := lookup_config(src) in                  // May return null
  match config_ptr with
  | Some(p) => 
      let tmp := ref !p + 1 in                             // Safe `ref` (non-null)
      p := !tmp                                            // Write back via safe deref
  | None =>
      log("No config found for packet")                    // Handle null case
}*)

(*Safe memory allocation via ref (no need for null checks)

Explicit handling of potentially-null values via option *τ

Type-directed pattern matching ensures absence of undefined behavior

Compiler-inserted checks, not left to programmer discipline*)
