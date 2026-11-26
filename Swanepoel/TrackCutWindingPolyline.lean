module
public import Swanepoel.TrackCutOuterClosure
public import Swanepoel.PolygonSeparationAngles
@[expose] public section

noncomputable section
namespace Swanepoel

inductive PlaneChain : Plane→Plane→Type
  | nil (a : Plane) : PlaneChain a a
  | cons (a b c : Plane) (tail : PlaneChain b c) : PlaneChain a c

namespace PlaneChain

def trace {a b : Plane} : PlaneChain a b → Set Plane
  | .nil a => {a}
  | .cons a b _ p => segment ℝ a b ∪ p.trace

def angle {a b : Plane} : PlaneChain a b → Plane→ℝ
  | .nil _ => fun _ => 0
  | .cons a b _ p => fun z => segmentAngle a b z+p.angle z

def single (a b : Plane) : PlaneChain a b := .cons a b b (.nil b)

def append {a b c : Plane} : PlaneChain a b → PlaneChain b c → PlaneChain a c
  | .nil _,q => q
  | .cons a d _ p,q => .cons a d c (p.append q)

theorem start_mem_trace {a b : Plane} (p : PlaneChain a b) : a∈p.trace := by
  cases p with
  | nil a => exact Set.mem_singleton a
  | cons a b c p => exact Or.inl (left_mem_segment ℝ a b)

theorem end_mem_trace {a b : Plane} (p : PlaneChain a b) : b∈p.trace := by
  induction p with
  | nil a => exact Set.mem_singleton a
  | cons a b c p ih => exact Or.inr ih

theorem trace_single (a b : Plane) : (single a b).trace=segment ℝ a b := by
  simp only [single,trace]
  exact Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr (right_mem_segment ℝ a b))

theorem trace_append {a b c : Plane} (p : PlaneChain a b) (q : PlaneChain b c) :
    (p.append q).trace=p.trace∪q.trace := by
  induction p with
  | nil a =>
    simp only [append,trace]
    exact (Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr q.start_mem_trace)).symm
  | cons a b d p ih => simp only [append,trace,ih,Set.union_assoc]

theorem angle_append {a b c : Plane} (p : PlaneChain a b) (q : PlaneChain b c) (z : Plane) :
    (p.append q).angle z=p.angle z+q.angle z := by
  induction p with
  | nil => simp [append,angle]
  | cons a b d p ih => simp only [append,angle,ih,add_assoc]

theorem angle_coe {a b : Plane} (p : PlaneChain a b) {z : Plane} (hz : z∉p.trace) :
    (p.angle z : Real.Angle)=
      (Complex.arg (planeComplex b-planeComplex z) : Real.Angle)-
        (Complex.arg (planeComplex a-planeComplex z) : Real.Angle) := by
  induction p with
  | nil a => simp [angle]
  | cons a b c p ih =>
    have hseg : z∉segment ℝ a b := fun h => hz (Or.inl h)
    have htail : z∉p.trace := fun h => hz (Or.inr h)
    have ha : a≠z := by intro he; exact hseg (he ▸ left_mem_segment ℝ a b)
    have hb : b≠z := by intro he; exact hseg (he ▸ right_mem_segment ℝ a b)
    rw [angle,Real.Angle.coe_add,segmentAngle_coe _ _ _ ha hb,ih htail]
    abel

theorem continuousAt_angle {a b : Plane} (p : PlaneChain a b) {z : Plane}
    (hz : z∉p.trace) : ContinuousAt p.angle z := by
  induction p with
  | nil => exact continuousAt_const
  | cons a b c p ih =>
    change ContinuousAt (fun w => segmentAngle a b w+p.angle w) z
    exact (continuousAt_segmentAngle (fun h => hz (Or.inl h))).add
      (ih (fun h => hz (Or.inr h)))

theorem closed_angle_mem_zmultiples {a : Plane} (p : PlaneChain a a) {z : Plane}
    (hz : z∉p.trace) : p.angle z∈AddSubgroup.zmultiples (2*Real.pi) := by
  apply AddSubgroup.mem_zmultiples_iff.mpr
  apply Real.Angle.coe_eq_zero_iff.mp
  rw [p.angle_coe hz,sub_self]

theorem closed_angle_constant {a : Plane} (p : PlaneChain a a) {F : Set Plane}
    (hF : IsPreconnected F) (hdis : Disjoint F p.trace) {x y : Plane} (hx : x∈F) (hy : y∈F) :
    p.angle x=p.angle y := by
  have hd : IsDiscrete ((AddSubgroup.zmultiples (2*Real.pi) : AddSubgroup ℝ) : Set ℝ) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  apply hF.constant_of_mapsTo hd ?_ ?_ hx hy
  · intro z hz
    exact (p.continuousAt_angle (Set.disjoint_left.mp hdis hz)).continuousWithinAt
  · intro z hz
    exact p.closed_angle_mem_zmultiples (Set.disjoint_left.mp hdis hz)

theorem closed_angle_constant_on_component {a : Plane} (p : PlaneChain a a) {x y : Plane}
    (hx : x∉p.trace) (hy : y∈connectedComponentIn p.traceᶜ x) : p.angle x=p.angle y := by
  apply p.closed_angle_constant isPreconnected_connectedComponentIn ?_ (mem_connectedComponentIn hx) hy
  exact Set.disjoint_left.mpr (fun z hz => connectedComponentIn_subset _ _ hz)

def windingIndex {a : Plane} (p : PlaneChain a a) (z : Plane) : ℤ :=
  ⌊p.angle z/(2*Real.pi)⌋

theorem windingIndex_spec {a : Plane} (p : PlaneChain a a) {z : Plane} (hz : z∉p.trace) :
    (p.windingIndex z : ℝ)*(2*Real.pi)=p.angle z := by
  obtain ⟨k,hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (p.closed_angle_mem_zmultiples hz)
  have hratio : p.angle z/(2*Real.pi)=(k : ℝ) := by
    rw [← hk,zsmul_eq_mul]
    exact mul_div_cancel_right₀ _ (by positivity : (2*Real.pi : ℝ)≠0)
  simp only [windingIndex,hratio,Int.floor_intCast]
  simpa only [zsmul_eq_mul] using hk

theorem windingIndex_constant {a : Plane} (p : PlaneChain a a) {F : Set Plane}
    (hF : IsPreconnected F) (hdis : Disjoint F p.trace) {x y : Plane} (hx : x∈F) (hy : y∈F) :
    p.windingIndex x=p.windingIndex y := by
  unfold windingIndex
  rw [p.closed_angle_constant hF hdis hx hy]

end PlaneChain

theorem planeChain_of_segment_reachable {F : Set Plane} {a b : Plane} (ha : a∈F)
    (hab : Relation.ReflTransGen (planeSegmentStep F) a b) :
    ∃ p : PlaneChain a b, p.trace⊆F := by
  revert ha
  induction hab using Relation.ReflTransGen.head_induction_on with
  | refl => intro ha; exact ⟨.nil _,Set.singleton_subset_iff.mpr ha⟩
  | @head a b hab hbc ih =>
    intro ha
    obtain ⟨p,hp⟩ := ih (hab (right_mem_segment ℝ a b))
    exact ⟨.cons a b _ p,Set.union_subset hab hp⟩

end Swanepoel
