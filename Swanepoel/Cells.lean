module
public import Swanepoel.Rhombi
public import Swanepoel.RhombusArea
@[expose] public section

noncomputable section
namespace Swanepoel

structure RhombusCell {n : ℕ} (G : PennyGraph n) where
  a : Fin n
  b : Fin n
  c : Fin n
  d : Fin n
  ac : a ≠ c
  bd : b ≠ d
  ab : G.graph.Adj a b
  bc : G.graph.Adj b c
  cd : G.graph.Adj c d
  da : G.graph.Adj d a

namespace RhombusCell
variable {n : ℕ} {G : PennyGraph n} (C : RhombusCell G)

def u : Plane := G.point C.b-G.point C.a
def v : Plane := G.point C.d-G.point C.a

theorem parallelogram : G.point C.a+G.point C.c=G.point C.b+G.point C.d :=
  G.four_cycle_parallelogram C.a C.b C.c C.d C.ac C.bd C.ab C.bc C.cd C.da

theorem opposite_vectors : G.point C.b-G.point C.a=G.point C.c-G.point C.d :=
  G.four_cycle_opposite_edges C.a C.b C.c C.d C.ac C.bd C.ab C.bc C.cd C.da

theorem area_lower (ht : G.TriangleFree) : Real.sqrt 3/2 < |cross2 C.u C.v| := by
  have hc : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
  have hminus : C.u-C.v=G.point C.b-G.point C.d := by dsimp [u,v]; abel
  have hplus : C.u+C.v=G.point C.c-G.point C.a := by dsimp [u,v]; rw [hc]; abel
  apply unit_rhombus_area_lower
  · simpa only [u, ← dist_eq_norm] using C.ab.symm.2
  · simpa only [v, ← dist_eq_norm] using C.da.2
  · rw [hminus, ← dist_eq_norm]
    exact G.two_step_dist_gt_one ht C.b C.a C.d C.bd C.ab.symm C.da.symm
  · rw [hplus, ← dist_eq_norm]
    simpa [dist_comm] using G.two_step_dist_gt_one ht C.a C.b C.c C.ac C.ab C.bc

def midpoint2 (x y : Plane) : Plane := (1/2 : ℝ) • (x+y)

theorem spine_step :
    midpoint2 (G.point C.d) (G.point C.c)-midpoint2 (G.point C.a) (G.point C.b)=C.v := by
  have hc : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
  have hv : (G.point C.d+G.point C.c)-(G.point C.a+G.point C.b)=(2 : ℝ) • C.v := by
    rw [two_smul, hc]
    dsimp [v]
    abel
  unfold midpoint2
  rw [← smul_sub, hv, smul_smul]
  norm_num

theorem no_other_vertices (i : Fin n) (t s : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hi : G.point i-G.point C.a=t • C.u+s • C.v) :
    i=C.a ∨ i=C.b ∨ i=C.c ∨ i=C.d := by
  by_contra hn
  simp only [not_or] at hn
  have hu : ‖C.u‖=1 := by simpa only [u, ← dist_eq_norm] using C.ab.symm.2
  have hv : ‖C.v‖=1 := by simpa only [v, ← dist_eq_norm] using C.da.2
  have hc : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
  have hb' : (G.point i-G.point C.a)-C.u=G.point i-G.point C.b := by dsimp [u]; abel
  have hd' : (G.point i-G.point C.a)-C.v=G.point i-G.point C.d := by dsimp [v]; abel
  have hc' : (G.point i-G.point C.a)-(C.u+C.v)=G.point i-G.point C.c := by
    dsimp [u,v]
    rw [hc]
    abel
  have hcover := unit_cell_covering C.u C.v (G.point i-G.point C.a) hu hv
    t s ht0 ht1 hs0 hs1 hi
  rw [hb',hd',hc'] at hcover
  simp only [← dist_eq_norm] at hcover
  rcases hcover with ha | hb | hd | hc
  · exact (not_lt_of_ge (G.separated i C.a hn.1)) ha
  · exact (not_lt_of_ge (G.separated i C.b hn.2.1)) hb
  · exact (not_lt_of_ge (G.separated i C.d hn.2.2.2)) hd
  · exact (not_lt_of_ge (G.separated i C.c hn.2.2.1)) hc

end RhombusCell

abbrev OrientedEdge {n : ℕ} (G : PennyGraph n) :=
  {e : Fin n × Fin n // G.graph.Adj e.1 e.2}

def carriedVector {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) : Plane :=
  G.point e.val.2-G.point e.val.1

def CellStep {n : ℕ} {G : PennyGraph n} (e f : OrientedEdge G) : Prop :=
  ∃ C : RhombusCell G, e.val=(C.a,C.b) ∧ f.val=(C.d,C.c)

theorem CellStep.vector_eq {n : ℕ} {G : PennyGraph n} {e f : OrientedEdge G}
    (h : CellStep e f) : carriedVector e=carriedVector f := by
  obtain ⟨C,he,hf⟩ := h
  simpa only [carriedVector, he, hf] using C.opposite_vectors

theorem track_carried_direction {n : ℕ} {G : PennyGraph n} {e f : OrientedEdge G}
    (h : Relation.ReflTransGen CellStep e f) : carriedVector e=carriedVector f := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans h.vector_eq

end Swanepoel
