module
public import Swanepoel.Cells
@[expose] public section

noncomputable section
namespace Swanepoel

theorem plane_gram_identity (u v w : Plane) :
    ‖u‖^2*‖v‖^2*‖w‖^2+2*inner ℝ u v*inner ℝ v w*inner ℝ w u-
      ‖u‖^2*(inner ℝ v w)^2-‖v‖^2*(inner ℝ w u)^2-
      ‖w‖^2*(inner ℝ u v)^2=0 := by
  simp [EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem no_three_separated_unit_directions (u v w : Plane)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (hw : ‖w‖=1)
    (huv : |inner ℝ u v| < 1/2) (hvw : |inner ℝ v w| < 1/2) :
    ¬ |inner ℝ w u| < 1/2 := by
  intro hwu
  have hsq (x : ℝ) (hx : |x| < 1/2) : x^2 < 1/4 := by
    nlinarith [sq_abs x, abs_nonneg x]
  have hab : |inner ℝ u v| * |inner ℝ v w| ≤ (1/2 : ℝ)*(1/2) :=
    mul_le_mul (le_of_lt huv) (le_of_lt hvw) (abs_nonneg _) (by norm_num)
  have habc : |inner ℝ u v*inner ℝ v w*inner ℝ w u| ≤ (1/8 : ℝ) := by
    rw [abs_mul,abs_mul]
    have h := mul_le_mul hab (le_of_lt hwu) (abs_nonneg (inner ℝ w u))
      (by norm_num : (0 : ℝ) ≤ (1/2)*(1/2))
    nlinarith
  have hg := plane_gram_identity u v w
  rw [hu,hv,hw] at hg
  have hl := (abs_le.mp habc).1
  nlinarith [hsq _ huv, hsq _ hvw, hsq _ hwu]

theorem RhombusCell.abs_inner_lt_half {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (ht : G.TriangleFree) : |inner ℝ C.u C.v| < 1/2 := by
  have hu : ‖C.u‖=1 := by simpa only [RhombusCell.u, ← dist_eq_norm] using C.ab.symm.2
  have hv : ‖C.v‖=1 := by simpa only [RhombusCell.v, ← dist_eq_norm] using C.da.2
  have hc := C.area_lower ht
  have he := cross2_sq_add_inner_sq C.u C.v
  rw [hu,hv] at he
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsn := Real.sqrt_nonneg (3 : ℝ)
  have hd : (3/4 : ℝ) < cross2 C.u C.v^2 := by
    nlinarith [sq_abs (cross2 C.u C.v)]
  have hi : (inner ℝ C.u C.v)^2 < (1/4 : ℝ) := by nlinarith
  rw [abs_lt]
  constructor <;> nlinarith

def SameLine (u v : Plane) : Prop := u=v ∨ u= -v

theorem SameLine.refl (u : Plane) : SameLine u u := Or.inl rfl
theorem SameLine.symm {u v : Plane} (h : SameLine u v) : SameLine v u := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    rw [h, neg_neg]

theorem SameLine.trans {u v w : Plane} (huv : SameLine u v) (hvw : SameLine v w) :
    SameLine u w := by
  rcases huv with rfl | h <;> rcases hvw with rfl | h'
  · exact SameLine.refl _
  · exact Or.inr h'
  · exact Or.inr h
  · left
    rw [h,h',neg_neg]

theorem SameLine.abs_inner_eq {u u' v v' : Plane}
    (hu : SameLine u u') (hv : SameLine v v') :
    |inner ℝ u v|=|inner ℝ u' v'| := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp

end Swanepoel
