module
public import Swanepoel.DirectionPacking
@[expose] public section

noncomputable section
namespace Swanepoel

theorem inner_cross_identity (e v w : Plane) :
    inner ℝ e v*inner ℝ e w+cross2 e v*cross2 e w=‖e‖^2*inner ℝ v w := by
  simp [cross2, EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem unit_cross_gt_sqrt (e v : Plane) (he : ‖e‖=1) (hv : ‖v‖=1)
    (hi : |inner ℝ e v| < 1/2) (hc : 0 < cross2 e v) :
    Real.sqrt 3/2 < cross2 e v := by
  have h := cross2_sq_add_inner_sq e v
  rw [he,hv] at h
  have hsq : (inner ℝ e v)^2 < (1/4 : ℝ) := by
    nlinarith [sq_abs (inner ℝ e v),abs_nonneg (inner ℝ e v)]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsn := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

theorem unit_vectors_same_side_close (e v w : Plane) (he : ‖e‖=1)
    (hv : ‖v‖=1) (hw : ‖w‖=1)
    (hiv : |inner ℝ e v| < 1/2) (hiw : |inner ℝ e w| < 1/2)
    (hcv : 0 < cross2 e v) (hcw : 0 < cross2 e w) : ‖v-w‖ < 1 := by
  have hcv' := unit_cross_gt_sqrt e v he hv hiv hcv
  have hcw' := unit_cross_gt_sqrt e w he hw hiw hcw
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hspos : (0 : ℝ) < Real.sqrt 3/2 := by positivity
  have hmul := mul_lt_mul hcv' (le_of_lt hcw') hspos (le_of_lt hcv)
  have hprod : (3/4 : ℝ) < cross2 e v*cross2 e w := by nlinarith
  have hab : |inner ℝ e v*inner ℝ e w| ≤ (1/4 : ℝ) := by
    rw [abs_mul]
    have hh := mul_le_mul (le_of_lt hiv) (le_of_lt hiw)
      (abs_nonneg (inner ℝ e w)) (by norm_num : (0 : ℝ) ≤ 1/2)
    nlinarith
  have hid := inner_cross_identity e v w
  rw [he] at hid
  have hi : (1/2 : ℝ) < inner ℝ v w := by nlinarith [(abs_le.mp hab).1]
  have hnorm := norm_sub_sq_real v w
  rw [hv,hw] at hnorm
  nlinarith [norm_nonneg (v-w)]

theorem RhombusCell.unique_positive_side {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (C D : RhombusCell G) (ha : C.a=D.a) (hb : C.b=D.b)
    (hC : 0 < cross2 C.u C.v) (hD : 0 < cross2 D.u D.v) : C.d=D.d ∧ C.c=D.c := by
  have hu : C.u=D.u := by simp only [RhombusCell.u,ha,hb]
  have he : ‖C.u‖=1 := by simpa only [RhombusCell.u, ← dist_eq_norm] using C.ab.symm.2
  have hv : ‖C.v‖=1 := by simpa only [RhombusCell.v, ← dist_eq_norm] using C.da.2
  have hw : ‖D.v‖=1 := by simpa only [RhombusCell.v, ← dist_eq_norm] using D.da.2
  have hiw : |inner ℝ C.u D.v| < 1/2 := by rw [hu]; exact D.abs_inner_lt_half ht
  have hcross : 0 < cross2 C.u D.v := by rw [hu]; exact hD
  have hclose := unit_vectors_same_side_close C.u C.v D.v he hv hw
    (C.abs_inner_lt_half ht) hiw hC hcross
  have hdiff : C.v-D.v=G.point C.d-G.point D.d := by
    dsimp [RhombusCell.v]
    rw [ha]
    abel
  rw [hdiff, ← dist_eq_norm] at hclose
  have hd : C.d=D.d := by
    by_contra hne
    exact (not_lt_of_ge (G.separated C.d D.d hne)) hclose
  refine ⟨hd,?_⟩
  have hCp := C.parallelogram
  rw [ha,hb,hd] at hCp
  exact G.point_injective (add_left_cancel (hCp.trans D.parallelogram.symm))

end Swanepoel
