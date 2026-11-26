module
public import Swanepoel.SpokePairLoops
@[expose] public section

noncomputable section
namespace Swanepoel
open Set

theorem segmentAngle_reverse {a b z : Plane} (hz : z∉segment ℝ a b) :
    segmentAngle b a z= -segmentAngle a b z := by
  have hz' : planeComplex z∉segment ℝ (planeComplex a) (planeComplex b) := by
    rwa [planeComplex_mem_segment_iff]
  have hslit := endpoint_ratio_mem_slitPlane hz'
  have hratio : (planeComplex a-planeComplex z)/(planeComplex b-planeComplex z)=
      ((planeComplex b-planeComplex z)/(planeComplex a-planeComplex z))⁻¹ := by rw [inv_div]
  unfold segmentAngle
  rw [hratio,Complex.arg_inv,ite_eq_right (Complex.slitPlane_arg_ne_pi hslit)]

namespace PlaneChain

def conjugate {b : Plane} (p : PlaneChain b b) (a : Plane) : PlaneChain a a :=
  (single a b).append (p.append (single b a))

theorem trace_conjugate {b : Plane} (p : PlaneChain b b) (a : Plane) :
    (p.conjugate a).trace=segment ℝ a b∪p.trace := by
  simp only [conjugate,trace_append,trace_single,segment_symm (𝕜 := ℝ) b a]
  ext z
  simp only [Set.mem_union]
  tauto

theorem angle_conjugate {b : Plane} (p : PlaneChain b b) (a z : Plane)
    (hz : z∉segment ℝ a b) : (p.conjugate a).angle z=p.angle z := by
  simp only [conjugate,angle_append,single_angle,segmentAngle_reverse hz]
  ring

theorem windingIndex_conjugate {b : Plane} (p : PlaneChain b b) (a z : Plane)
    (hz : z∉segment ℝ a b) : (p.conjugate a).windingIndex z=p.windingIndex z := by
  unfold windingIndex
  rw [p.angle_conjugate a z hz]

end PlaneChain

theorem symmetric_segment_subset_halves (m x : Plane) :
    segment ℝ (m-x) (m+x)⊆segment ℝ m (m-x)∪segment ℝ m (m+x) := by
  intro z hz
  rw [segment_eq_image] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  by_cases h : t≤1/2
  · left
    rw [segment_eq_image]
    refine ⟨1-2*t,⟨by linarith [ht.2],by linarith [ht.1]⟩,?_⟩
    module
  · right
    rw [segment_eq_image]
    refine ⟨2*t-1,⟨by linarith,by linarith [ht.2]⟩,?_⟩
    module

theorem normal_offset_not_on_transverse_connector (m v : Plane) (hv : ‖v‖=1)
    (δ t : ℝ) (ht : t≠0) : m+t • v∉segment ℝ m (m-δ • quarterTurn v) := by
  have horth : inner ℝ v (quarterTurn v)=0 := by
    simp [quarterTurn,PiLp.inner_apply,Fin.sum_univ_two]
    ring
  intro hz
  rw [segment_eq_image] at hz
  obtain ⟨r,_,heq⟩ := hz
  have hvec : (1-r) • m+r • (m-δ • quarterTurn v)-m=(-r*δ) • quarterTurn v := by module
  have hh := congrArg (fun z : Plane => inner ℝ v (z-m)) heq
  rw [hvec,real_inner_smul_right,horth,mul_zero,add_sub_cancel_left,
    real_inner_smul_right,real_inner_self_eq_norm_sq,hv] at hh
  norm_num at hh
  exact ht hh.symm

theorem symmetric_normal_probe (m v : Plane) (δ r : ℝ) :
    windingNormalProbe (m-δ • quarterTurn v) (m+δ • quarterTurn v) r=m+(2*δ*r) • v := by
  ext i
  fin_cases i <;> simp [windingNormalProbe,quarterTurn] <;> ring

theorem symmetric_normal_loop_winding_jump (m v : Plane) (hv : ‖v‖=1)
    (δ : ℝ) (hδ : 0<δ)
    (rest : PlaneChain (m+δ • quarterTurn v) (m-δ • quarterTurn v)) (hm : m∉rest.trace) :
    ∃ ε : ℝ,0<ε ∧ ∀ r : ℝ,0<r → r<ε →
      let loop := ((PlaneChain.single (m-δ • quarterTurn v) (m+δ • quarterTurn v)).append rest).conjugate m
      loop.windingIndex (m+(-(2*δ*r)) • v)=loop.windingIndex (m+(2*δ*r) • v)+1 := by
  let a := m-δ • quarterTurn v
  let b := m+δ • quarterTurn v
  have hne : a≠b := by
    intro h
    have hh := congrArg (fun z : Plane => cross2 v (z-m)) h
    have ha : a-m= -δ • quarterTurn v := by dsimp [a]; module
    have hb : b-m=δ • quarterTurn v := by dsimp [b]; module
    rw [ha,hb,cross2_smul_right,cross2_smul_right,cross_quarterTurn,hv] at hh
    nlinarith only [hh,hδ]
  have hmid : (1/2:ℝ) • (a+b)=m := by dsimp [a,b]; module
  obtain ⟨ε,hε,hjump⟩ := PlaneChain.segment_loop_winding_jump hne rest (hmid ▸ hm)
  refine ⟨ε,hε,?_⟩
  intro r hr hre
  let p := (PlaneChain.single a b).append rest
  have hj := (hjump r hr hre).2.2.1
  have hpos : 2*δ*r≠0 := ne_of_gt (by positivity)
  have hneg : -(2*δ*r)≠0 := neg_ne_zero.mpr hpos
  change (p.conjugate m).windingIndex _=(p.conjugate m).windingIndex _+1
  rw [p.windingIndex_conjugate m _ (normal_offset_not_on_transverse_connector m v hv δ _ hneg),
    p.windingIndex_conjugate m _ (normal_offset_not_on_transverse_connector m v hv δ _ hpos)]
  simpa only [a,b,symmetric_normal_probe,show 2*δ*(-r)= -(2*δ*r) by ring] using hj

end Swanepoel
