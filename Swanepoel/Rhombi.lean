module
public import Swanepoel.Foundation
public import Mathlib.Geometry.Euclidean.Basic
@[expose] public section

noncomputable section
namespace Swanepoel

theorem unit_four_cycle_parallelogram (a b c d : Plane) (hac : a ≠ c) (hbd : b ≠ d)
    (hab : dist a b=1) (hbc : dist b c=1) (hcd : dist c d=1) (hda : dist d a=1) :
    a+c=b+d := by
  let p := a+c-b
  have hpa : dist p a=1 := by
    have he : p-a=c-b := by dsimp [p]; abel
    rw [dist_eq_norm, he, ← dist_eq_norm]
    simpa [dist_comm] using hbc
  have hpc : dist p c=1 := by
    have he : p-c=a-b := by dsimp [p]; abel
    rw [dist_eq_norm, he, ← dist_eq_norm]
    exact hab
  have hpb : p ≠ b := by
    intro he
    have hac' : a+c=b+b := (sub_eq_iff_eq_add).mp he
    have hc : c=b+b-a := (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using hac')
    have hu : ‖a-b‖=1 := by simpa only [dist_eq_norm] using hab
    have hm : ‖(a-b)-(d-b)‖=1 := by
      have he' : (a-b)-(d-b)=a-d := by abel
      rw [he', ← dist_eq_norm]
      simpa [dist_comm] using hda
    have hp : ‖(a-b)+(d-b)‖=1 := by
      have he' : (a-b)+(d-b)=-(c-d) := by rw [hc]; abel
      rw [he', norm_neg, ← dist_eq_norm]
      exact hcd
    have hs := norm_sub_sq_real (a-b) (d-b)
    have ha := norm_add_sq_real (a-b) (d-b)
    rw [hu, hm] at hs
    rw [hu, hp] at ha
    have hz : ‖d-b‖=0 := by nlinarith [norm_nonneg (d-b)]
    exact hbd (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  have he := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    (V := Plane) (P := Plane) (by simp [Plane]) hac hbd
    (by simpa [dist_comm] using hab) hda hpa hbc
    (by simpa [dist_comm] using hcd) hpc
  have hpd : p=d := he.resolve_left hpb
  have heq : a+c=d+b := (sub_eq_iff_eq_add).mp hpd
  simpa [add_comm] using heq

theorem PennyGraph.four_cycle_parallelogram {n : ℕ} (G : PennyGraph n)
    (a b c d : Fin n) (hac : a ≠ c) (hbd : b ≠ d)
    (hab : G.graph.Adj a b) (hbc : G.graph.Adj b c)
    (hcd : G.graph.Adj c d) (hda : G.graph.Adj d a) :
    G.point a+G.point c=G.point b+G.point d :=
  unit_four_cycle_parallelogram _ _ _ _
    (fun h => hac (G.point_injective h)) (fun h => hbd (G.point_injective h))
    hab.2 hbc.2 hcd.2 hda.2

theorem PennyGraph.four_cycle_opposite_edges {n : ℕ} (G : PennyGraph n)
    (a b c d : Fin n) (hac : a ≠ c) (hbd : b ≠ d)
    (hab : G.graph.Adj a b) (hbc : G.graph.Adj b c)
    (hcd : G.graph.Adj c d) (hda : G.graph.Adj d a) :
    G.point b-G.point a=G.point c-G.point d := by
  have he := G.four_cycle_parallelogram a b c d hac hbd hab hbc hcd hda
  apply (sub_eq_sub_iff_add_eq_add).mpr
  simpa [add_comm] using he.symm

end Swanepoel
