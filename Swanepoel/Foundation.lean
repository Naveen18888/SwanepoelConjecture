module
public import Swanepoel.Definitions
@[expose] public section

noncomputable section
namespace Swanepoel

theorem PennyGraph.point_injective {n : ℕ} (G : PennyGraph n) :
    Function.Injective G.point := by
  intro i j hij
  by_contra hne
  have h := G.separated i j hne
  rw [hij, dist_self] at h
  norm_num at h

theorem PennyGraph.dist_gt_one_of_nonadj {n : ℕ} (G : PennyGraph n)
    (i j : Fin n) (hne : i ≠ j) (hnot : ¬ G.graph.Adj i j) :
    1 < dist (G.point i) (G.point j) := by
  have hsep := G.separated i j hne
  have he : dist (G.point i) (G.point j) ≠ 1 := fun h => hnot ⟨hne, h⟩
  exact lt_of_le_of_ne hsep (Ne.symm he)

theorem PennyGraph.two_step_dist_gt_one {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (a b c : Fin n) (hne : a ≠ c)
    (hab : G.graph.Adj a b) (hbc : G.graph.Adj b c) :
    1 < dist (G.point a) (G.point c) :=
  G.dist_gt_one_of_nonadj a c hne (fun hac => ht a b c hab hbc hac.symm)

theorem PennyGraph.two_step_inner_lt_half {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (a b c : Fin n) (hne : a ≠ c)
    (hab : G.graph.Adj a b) (hbc : G.graph.Adj b c) :
    inner ℝ (G.point a-G.point b) (G.point c-G.point b) < 1/2 := by
  have hd := G.two_step_dist_gt_one ht a b c hne hab hbc
  have he : (G.point a-G.point b)-(G.point c-G.point b) = G.point a-G.point c := by abel
  have hs := norm_sub_sq_real (G.point a-G.point b) (G.point c-G.point b)
  rw [he] at hs
  simp only [← dist_eq_norm] at hs
  rw [hab.2, show dist (G.point c) (G.point b) = 1 by simpa [dist_comm] using hbc.2] at hs
  nlinarith [sq_nonneg (dist (G.point a) (G.point c)-1)]

theorem segment_variance (a b c d : Plane) (t s : ℝ) :
    (1-t)*(1-s)*‖a-c‖^2 + (1-t)*s*‖a-d‖^2 +
      t*(1-s)*‖b-c‖^2 + t*s*‖b-d‖^2 -
      t*(1-t)*‖a-b‖^2 - s*(1-s)*‖c-d‖^2 =
    ‖((1-t) • a+t • b)-((1-s) • c+s • d)‖^2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_comm]
  ring

theorem separated_unit_segments (a b c d : Plane)
    (hab : dist a b = 1) (hcd : dist c d = 1)
    (hac : 1 ≤ dist a c) (had : 1 ≤ dist a d)
    (hbc : 1 ≤ dist b c) (hbd : 1 ≤ dist b d)
    (t s : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1-t) • a+t • b ≠ (1-s) • c+s • d := by
  intro heq
  have hd (x y : Plane) (h : 1 ≤ dist x y) : 1 ≤ ‖x-y‖^2 := by
    rw [← dist_eq_norm]
    nlinarith [sq_nonneg (dist x y-1)]
  have hw1 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hs1)
  have hw2 := mul_nonneg (sub_nonneg.mpr ht1) hs0
  have hw3 := mul_nonneg ht0 (sub_nonneg.mpr hs1)
  have hw4 := mul_nonneg ht0 hs0
  have h1 := mul_le_mul_of_nonneg_left (hd a c hac) hw1
  have h2 := mul_le_mul_of_nonneg_left (hd a d had) hw2
  have h3 := mul_le_mul_of_nonneg_left (hd b c hbc) hw3
  have h4 := mul_le_mul_of_nonneg_left (hd b d hbd) hw4
  have hv := segment_variance a b c d t s
  rw [heq, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hv
  have hAB : ‖a-b‖ = 1 := by simpa only [dist_eq_norm] using hab
  have hCD : ‖c-d‖ = 1 := by simpa only [dist_eq_norm] using hcd
  rw [hAB, hCD] at hv
  nlinarith [sq_nonneg (2*t-1), sq_nonneg (2*s-1)]

theorem PennyGraph.disjoint_unit_edges {n : ℕ} (G : PennyGraph n)
    (a b c d : Fin n) (hab : G.graph.Adj a b) (hcd : G.graph.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (t s : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1-t) • G.point a+t • G.point b ≠ (1-s) • G.point c+s • G.point d :=
  separated_unit_segments _ _ _ _ hab.2 hcd.2
    (G.separated a c hac) (G.separated a d had)
    (G.separated b c hbc) (G.separated b d hbd) t s ht0 ht1 hs0 hs1

end Swanepoel
