import atlas.Atlas
/-!
  Reference gadgets shared by the tests and the proof layer.

  Kept in a leaf module (engine only, no problems, no IO) so that the
  proofs that pin the concrete gadget (`ProofsDecide`: the trident) do
  not import the test executable -- editing a test, a report or the
  audit no longer re-elaborates the proof chain and its build-time
  sweeps.
-/

namespace Atlas

/-- The trident: layer `p` carries the literal ports, layer `u` the
    triangle, and `gt gf gb` are the palette parts (T, F, B). Every edge
    is normalized. -/
def tridentGraph (p u gt gf gb : Nat) : List Edge :=
  let a := fun q (j : Nat) => Vertex.aux q j
  ([(a gt 0, a gf 0), (a gf 0, a gb 0), (a gb 0, a gt 0)] ++
   (List.range 3).map (fun i => (Vertex.lit i, a gb 0)) ++
   (List.range 3).map (fun i => (Vertex.lit i, a p i)) ++
   (List.range 3).map (fun i => (a p i, a u i)) ++
   (List.range 3).map (fun i => (a u i, a u ((i + 1) % 3))) ++
   (List.range 3).map (fun i => (a p i, a gt 0))).map normEdge

end Atlas
