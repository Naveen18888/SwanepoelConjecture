module
public import Swanepoel.RhombusEnumeration
@[expose] public section

noncomputable section
namespace Swanepoel

theorem RhombusCell.center_eq_quarter_sum {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) : C.center=(1/4 : ℝ) • ∑ i ∈ C.corners, G.point i := by
  classical
  have hab := C.ab.ne
  have hbc := C.bc.ne
  have hcd := C.cd.ne
  have had := C.da.ne.symm
  have hs : (∑ i ∈ C.corners, G.point i)=
      G.point C.a+G.point C.b+G.point C.c+G.point C.d := by
    simp [RhombusCell.corners,hab,hbc,hcd,had,C.ac,C.bd]
    abel
  rw [hs]
  have hc : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
  dsimp [RhombusCell.center,RhombusCell.midpoint2]
  rw [hc]
  module

theorem RhombusCell.center_of_corners {n : ℕ} {G : PennyGraph n}
    (C D : RhombusCell G) (hc : C.corners=D.corners) : C.center=D.center := by
  rw [C.center_eq_quarter_sum,D.center_eq_quarter_sum,hc]

end Swanepoel
