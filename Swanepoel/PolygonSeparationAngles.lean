module
public import Swanepoel.PolygonReduction
public import Mathlib.Analysis.Complex.Arg
public import Mathlib.Topology.Instances.ZMultiples
public import Mathlib.Topology.Connected.TotallyDisconnected
@[expose] public section

noncomputable section
namespace Swanepoel

def planeComplex : Plane →ₗ[ℝ] ℂ where
  toFun x := ⟨x 0,x 1⟩
  map_add' x y := by apply Complex.ext <;> simp
  map_smul' a x := by apply Complex.ext <;> simp [Complex.real_smul]

theorem planeComplex_injective : Function.Injective planeComplex := by
  intro x y h
  ext i
  fin_cases i
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

theorem continuous_planeComplex : Continuous planeComplex :=
  planeComplex.continuous_of_finiteDimensional

theorem planeComplex_mem_segment_iff (a b z : Plane) :
    planeComplex z∈segment ℝ (planeComplex a) (planeComplex b) ↔ z∈segment ℝ a b := by
  rw [mem_segment_iff_sameRay,mem_segment_iff_sameRay,← map_sub,← map_sub]
  exact planeComplex_injective.sameRay_map_iff

theorem endpoint_ratio_mem_slitPlane {a b z : ℂ} (hz : z∉segment ℝ a b) :
    (b-z)/(a-z)∈Complex.slitPlane := by
  have hza : a-z≠0 := by
    apply sub_ne_zero.mpr
    intro h
    apply hz
    rw [← h]
    exact left_mem_segment ℝ a b
  by_contra hslit
  have hh : ¬(0<((b-z)/(a-z)).re ∨ ((b-z)/(a-z)).im≠0) :=
    fun h => hslit (Complex.mem_slitPlane_iff.mpr h)
  push Not at hh
  let q := (b-z)/(a-z)
  have hreal : q=(q.re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact hh.2
  have hmul : b-z=(q.re : ℂ)*(a-z) := (div_eq_iff hza).mp hreal
  have hsmul : b-z=(-q.re) • (z-a) := by
    rw [Complex.real_smul]
    calc
      b-z=(q.re : ℂ)*(a-z) := hmul
      _ = ((-q.re : ℝ) : ℂ)*(z-a) := by push_cast; ring
  apply hz
  rw [mem_segment_iff_sameRay,hsmul]
  exact SameRay.sameRay_nonneg_smul_right (z-a)
    (by change 0≤ -((b-z)/(a-z)).re; linarith [hh.1])

def segmentAngle (a b z : Plane) : ℝ :=
  Complex.arg ((planeComplex b-planeComplex z)/(planeComplex a-planeComplex z))

theorem continuousAt_segmentAngle {a b z : Plane} (hz : z∉segment ℝ a b) :
    ContinuousAt (segmentAngle a b) z := by
  have hslit := endpoint_ratio_mem_slitPlane ((planeComplex_mem_segment_iff a b z).not.mpr hz)
  have hne : planeComplex a-planeComplex z≠0 := by
    apply sub_ne_zero.mpr
    intro h
    apply hz
    rw [← planeComplex_injective h]
    exact left_mem_segment ℝ a b
  have hc : ContinuousAt (fun w : Plane =>
      (planeComplex b-planeComplex w)/(planeComplex a-planeComplex w)) z :=
    (continuous_const.sub continuous_planeComplex).continuousAt.div
      (continuous_const.sub continuous_planeComplex).continuousAt hne
  exact ContinuousAt.comp (f := fun w : Plane =>
    (planeComplex b-planeComplex w)/(planeComplex a-planeComplex w))
    (Complex.continuousAt_arg hslit) hc

theorem segmentAngle_coe (a b z : Plane) (ha : a≠z) (hb : b≠z) :
    (segmentAngle a b z : Real.Angle)=
      (Complex.arg (planeComplex b-planeComplex z) : Real.Angle)-
        (Complex.arg (planeComplex a-planeComplex z) : Real.Angle) := by
  exact Complex.arg_div_coe_angle (sub_ne_zero.mpr (planeComplex_injective.ne hb))
    (sub_ne_zero.mpr (planeComplex_injective.ne ha))

theorem PennyGraph.edgeTrace_eq_segment {n : ℕ} (G : PennyGraph n) (a b : Fin n) :
    G.edgeTrace a b=segment ℝ (G.point a) (G.point b) := by
  rw [segment_eq_image]
  rfl

theorem PennyGraph.contactGraph_edgeTrace_subset {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) {a b : Fin n} (hab : (G.contactGraph S).Adj a b) :
    G.edgeTrace a b⊆G.subdrawing S := by
  obtain ⟨e,he,hab⟩ := hab
  have hsub : G.edgeTrace e.val.1 e.val.2⊆G.subdrawing S := by
    intro z hz
    exact Or.inr (Set.mem_iUnion.mpr ⟨e,Set.mem_iUnion.mpr ⟨he,hz⟩⟩)
  rcases Sym2.eq_iff.mp hab with h | h
  · simpa only [h.1,h.2] using hsub
  · rw [G.edgeTrace_reverse] at hsub
    simpa only [h.1,h.2] using hsub

end Swanepoel
