module
public import Swanepoel.TrackCutWindingJump
@[expose] public section

noncomputable section
namespace Swanepoel

inductive PositiveSpineChain {n : ℕ} (G : PennyGraph n) : OrientedEdge G→OrientedEdge G→Type
  | nil (s : OrientedEdge G) : PositiveSpineChain G s s
  | cons (s e t : OrientedEdge G) (step : PositiveCellStep s e)
      (tail : PositiveSpineChain G e t) : PositiveSpineChain G s t

namespace PositiveSpineChain
variable {n : ℕ} {G : PennyGraph n}

theorem reach {s t : OrientedEdge G} : PositiveSpineChain G s t →
    Relation.ReflTransGen PositiveCellStep s t
  | .nil _ => Relation.ReflTransGen.refl
  | .cons _ _ _ h p => p.reach.head h

def toPlane {s t : OrientedEdge G} : PositiveSpineChain G s t →
    PlaneChain (edgeCenter s) (edgeCenter t)
  | .nil s => .nil (edgeCenter s)
  | .cons s e t _ p => .cons (edgeCenter s) (edgeCenter e) (edgeCenter t) p.toPlane

def append {s t u : OrientedEdge G} : PositiveSpineChain G s t →
    PositiveSpineChain G t u → PositiveSpineChain G s u
  | .nil _,q => q
  | .cons s e _ h p,q => .cons s e u h (p.append q)

def single {e f : OrientedEdge G} (h : PositiveCellStep e f) : PositiveSpineChain G e f :=
  .cons e f f h (.nil f)

theorem exists_of_reach {s t : OrientedEdge G} (h : Relation.ReflTransGen PositiveCellStep s t) :
    Nonempty (PositiveSpineChain G s t) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨.nil _⟩
  | @head s e hse het ih =>
    obtain ⟨p⟩ := ih
    exact ⟨.cons s e _ hse p⟩

theorem toPlane_append {s t u : OrientedEdge G} (p : PositiveSpineChain G s t)
    (q : PositiveSpineChain G t u) : (p.append q).toPlane=p.toPlane.append q.toPlane := by
  induction p with
  | nil => rfl
  | cons s e t h p ih => simp only [append,toPlane,PlaneChain.append,ih]

theorem toPlane_single {e f : OrientedEdge G} (h : PositiveCellStep e f) :
    (single h).toPlane=PlaneChain.single (edgeCenter e) (edgeCenter f) := rfl

theorem decompose (ht : G.TriangleFree) {s t e f : OrientedEdge G}
    (p : PositiveSpineChain G s t) (htop : ¬∃g, PositiveCellStep t g)
    (he : OnSpine s t e) (hef : PositiveCellStep e f) :
    ∃ before : PositiveSpineChain G s e, ∃ after : PositiveSpineChain G f t,
      p=(before.append (single hef)).append after := by
  induction p generalizing e f with
  | nil s =>
    have heq := onSpine_refl_eq he
    subst e
    exact False.elim (htop ⟨f,hef⟩)
  | cons s d t hsd tail ih =>
    by_cases hse : e=s
    · subst e
      have hfd := positive_step_functional ht hef hsd
      subst f
      exact ⟨.nil s,tail,rfl⟩
    · have hde : Relation.ReflTransGen PositiveCellStep d e := by
        rcases he.1.cases_head with h | ⟨g,hsg,hge⟩
        · exact False.elim (hse h.symm)
        · have hdg := positive_step_functional ht hsd hsg
          simpa only [hdg] using hge
      obtain ⟨before,after,hparts⟩ := ih htop ⟨hde,he.2⟩ hef
      refine ⟨.cons s d e hsd before,after,?_⟩
      rw [hparts]
      rfl

theorem trace_subset_track {s t : OrientedEdge G} (p : PositiveSpineChain G s t) :
    p.toPlane.trace⊆trackSpineTrace (edgeComponent s) := by
  induction p with
  | nil s => exact Set.singleton_subset_iff.mpr (Or.inl ⟨s,rfl,rfl⟩)
  | cons s e t h p ih =>
    apply Set.union_subset
    · exact fun z hz => Or.inr ⟨s,e,rfl,h,hz⟩
    · have hc := positive_path_component (Relation.ReflTransGen.single h)
      rwa [← hc] at ih

theorem height_bounds {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    {z : Plane} (hz : z∈p.toPlane.trace) :
    edgeHeight s≤cross2 (carriedVector s) z ∧ cross2 (carriedVector s) z≤edgeHeight t := by
  induction p with
  | nil s =>
    rw [Set.mem_singleton_iff.mp hz]
    exact ⟨le_rfl,le_rfl⟩
  | cons s d t hsd tail ih =>
    rcases hz with hz | hz
    · have hc : Convex ℝ {w : Plane | edgeHeight s≤cross2 (carriedVector s) w ∧
          cross2 (carriedVector s) w≤edgeHeight t} :=
        (convex_Icc _ _).linear_preimage (crossLinear (carriedVector s))
      have hs : edgeCenter s∈{w : Plane | edgeHeight s≤cross2 (carriedVector s) w ∧
          cross2 (carriedVector s) w≤edgeHeight t} :=
        ⟨le_rfl,positive_path_height_le (tail.reach.head hsd)⟩
      have hd : edgeCenter d∈{w : Plane | edgeHeight s≤cross2 (carriedVector s) w ∧
          cross2 (carriedVector s) w≤edgeHeight t} := by
        rw [hsd.to_cellStep.vector_eq]
        exact ⟨hsd.height_lt.le,positive_path_height_le tail.reach⟩
      exact hc.segment_subset hs hd hz
    · have hh := ih hz
      rw [hsd.to_cellStep.vector_eq]
      exact ⟨hsd.height_lt.le.trans hh.1,hh.2⟩

theorem complete_trace (ht : G.TriangleFree) {s t : OrientedEdge G}
    (p : PositiveSpineChain G s t) (hs : ¬∃g, PositiveCellStep g s)
    (htop : ¬∃g, PositiveCellStep t g) : p.toPlane.trace=trackSpineTrace (edgeComponent s) := by
  apply p.trace_subset_track.antisymm
  rw [complete_spine_trace_with_start ht hs htop p.reach]
  intro z hz
  rcases hz with hz | ⟨e,f,hse,hef,hft,hz⟩
  · rw [Set.mem_singleton_iff.mp hz]
    exact p.toPlane.start_mem_trace
  · obtain ⟨before,after,hparts⟩ := p.decompose ht htop ⟨hse,(Relation.ReflTransGen.single hef).trans hft⟩ hef
    rw [hparts,toPlane_append,toPlane_append,toPlane_single,PlaneChain.trace_append,
      PlaneChain.trace_append,PlaneChain.trace_single]
    exact Or.inl (Or.inr hz)

end PositiveSpineChain

namespace PlaneChain

theorem append_assoc {a b c d : Plane} (p : PlaneChain a b) (q : PlaneChain b c) (r : PlaneChain c d) :
    (p.append q).append r=p.append (q.append r) := by
  induction p with
  | nil => rfl
  | cons a b c p ih => simp only [append,ih]

theorem cyclic_trace {a b : Plane} (p : PlaneChain a b) (q : PlaneChain b a) :
    (p.append q).trace=(q.append p).trace := by
  rw [trace_append,trace_append,Set.union_comm]

theorem cyclic_angle {a b : Plane} (p : PlaneChain a b) (q : PlaneChain b a) (z : Plane) :
    (p.append q).angle z=(q.append p).angle z := by
  rw [angle_append,angle_append,add_comm]

theorem cyclic_windingIndex {a b : Plane} (p : PlaneChain a b) (q : PlaneChain b a) (z : Plane) :
    (p.append q).windingIndex z=(q.append p).windingIndex z := by
  unfold windingIndex
  rw [p.cyclic_angle q]

end PlaneChain
end Swanepoel
