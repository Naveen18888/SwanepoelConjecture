module
public import Swanepoel.CompleteSpines
@[expose] public section

noncomputable section
namespace Swanepoel

theorem cross2_add_right (e x y : Plane) : cross2 e (x+y)=cross2 e x+cross2 e y := by
  unfold cross2
  change e 0*(x 1+y 1)-e 1*(x 0+y 0)=_
  ring

theorem cross2_smul_right (e x : Plane) (a : ℝ) : cross2 e (a • x)=a*cross2 e x := by
  unfold cross2
  change e 0*(a*x 1)-e 1*(a*x 0)=_
  ring

def SpineCone (e x : Plane) : Prop := Real.sqrt 3 * |inner ℝ e x| < cross2 e x
def WeakSpineCone (e x : Plane) : Prop := x=0 ∨ SpineCone e x
def SharpNormal (e x : Plane) : Prop := 2*|inner ℝ e x| < ‖x‖

theorem SpineCone.add {e x y : Plane} (hx : SpineCone e x) (hy : SpineCone e y) :
    SpineCone e (x+y) := by
  unfold SpineCone at *
  rw [inner_add_right,cross2_add_right]
  have h := mul_le_mul_of_nonneg_left (abs_add_le (inner ℝ e x) (inner ℝ e y))
    (Real.sqrt_nonneg 3)
  nlinarith

theorem SpineCone.smul {e x : Plane} (hx : SpineCone e x) {a : ℝ} (ha : 0<a) :
    SpineCone e (a • x) := by
  unfold SpineCone at *
  rw [real_inner_smul_right,cross2_smul_right,abs_mul,abs_of_pos ha]
  nlinarith [mul_pos ha (sub_pos.mpr hx)]

theorem SpineCone.add_weak {e x y : Plane} (hx : SpineCone e x) (hy : WeakSpineCone e y) :
    SpineCone e (x+y) := by
  rcases hy with rfl | hy
  · simpa using hx
  · exact hx.add hy

theorem WeakSpineCone.add_strict {e x y : Plane} (hx : WeakSpineCone e x) (hy : SpineCone e y) :
    SpineCone e (x+y) := by
  rcases hx with rfl | hx
  · simpa using hy
  · exact hx.add hy

theorem SpineCone.sharpNormal {e x : Plane} (he : ‖e‖=1) (hx : SpineCone e x) :
    SharpNormal e x := by
  have hn : 0 ≤ Real.sqrt 3 * |inner ℝ e x| := by positivity
  have hc : 0 < cross2 e x := lt_of_le_of_lt hn hx
  have hs : (Real.sqrt 3 * |inner ℝ e x|)^2 < (cross2 e x)^2 :=
    (sq_lt_sq₀ hn (le_of_lt hc)).mpr hx
  have hroot : (Real.sqrt 3 * |inner ℝ e x|)^2=3*(inner ℝ e x)^2 := by
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),sq_abs]
  rw [hroot] at hs
  have hid := cross2_sq_add_inner_sq e x
  rw [he] at hid
  have hs2 : (2*|inner ℝ e x|)^2 < ‖x‖^2 := by nlinarith [sq_abs (inner ℝ e x)]
  exact (sq_lt_sq₀ (by positivity) (norm_nonneg x)).mp hs2

theorem SharpNormal.neg_iff (e x : Plane) : SharpNormal e (-x) ↔ SharpNormal e x := by
  simp [SharpNormal]

theorem SharpNormal.sameLine {e f x : Plane} (h : SameLine e f) (hx : SharpNormal e x) :
    SharpNormal f x := by
  rcases h with rfl | rfl
  · exact hx
  · simpa [SharpNormal] using hx

theorem no_common_sharpNormal (u v x : Plane) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (huv : |inner ℝ u v| < 1/2) (hux : SharpNormal u x) : ¬ SharpNormal v x := by
  intro hvx
  have hn : 0 < ‖x‖ := lt_of_le_of_lt (by positivity) hux
  let w := (‖x‖⁻¹ : ℝ) • x
  have hw : ‖w‖=1 := by
    simp [w,norm_smul,hn.ne']
  have hi (e : Plane) (he : SharpNormal e x) : |inner ℝ e w| < 1/2 := by
    dsimp [w]
    rw [real_inner_smul_right,abs_mul,abs_inv,abs_of_pos hn,inv_mul_eq_div]
    apply (div_lt_iff₀ hn).mpr
    unfold SharpNormal at he
    linarith
  exact no_three_separated_unit_directions u v w hu hv hw huv (hi v hvx)
    (by simpa only [real_inner_comm] using hi u hux)

theorem positive_path_vector {n : ℕ} {G : PennyGraph n} {e f : OrientedEdge G}
    (h : Relation.ReflTransGen PositiveCellStep e f) : carriedVector e=carriedVector f := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans h.to_cellStep.vector_eq

theorem PositiveCellStep.displacement_cone {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {e f : OrientedEdge G} (h : PositiveCellStep e f) :
    SpineCone (carriedVector e) (edgeCenter f-edgeCenter e) := by
  obtain ⟨C,he,hf,hpos⟩ := h
  have hu : carriedVector e=C.u := by simp only [carriedVector,he,RhombusCell.u]
  have hm : edgeCenter f-edgeCenter e=C.v := by simpa only [edgeCenter,he,hf] using C.spine_step
  rw [hu,hm]
  have hinner := C.abs_inner_lt_half ht
  have hcross := C.area_lower ht
  rw [abs_of_pos hpos] at hcross
  have hm := mul_lt_mul_of_pos_left hinner (by positivity : (0 : ℝ) < Real.sqrt 3)
  unfold SpineCone
  linarith

theorem positive_path_cone {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {e f : OrientedEdge G} (h : Relation.ReflTransGen PositiveCellStep e f) :
    WeakSpineCone (carriedVector e) (edgeCenter f-edgeCenter e) := by
  induction h with
  | refl => exact Or.inl (sub_self _)
  | @tail f g hfg hstep ih =>
    have hv := positive_path_vector hfg
    have hs := hstep.displacement_cone ht
    rw [← hv] at hs
    have ha := ih.add_strict hs
    have he : (edgeCenter f-edgeCenter e)+(edgeCenter g-edgeCenter f)=
        edgeCenter g-edgeCenter e := by abel
    rw [he] at ha
    exact Or.inr ha

end Swanepoel
