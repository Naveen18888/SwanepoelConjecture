module
public import Swanepoel.SpineMidpoints
public import Mathlib.Analysis.Convex.PathConnected
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
open scoped unitInterval

theorem strictMono_height_trans {x y z : Plane} (p : Path x y) (q : Path y z)
    (height : Plane → ℝ)
    (hp : StrictMono (fun t => height (p t)))
    (hq : StrictMono (fun t => height (q t))) :
    StrictMono (fun t => height ((p.trans q) t)) := by
  intro a b hab
  have hab' : (a : ℝ) < b := hab
  change height ((p.trans q) a) < height ((p.trans q) b)
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs with ha hb
  · apply hp
    change 2 * (a : ℝ) < 2 * (b : ℝ)
    linarith
  · have hleft : height (p ⟨2 * (a : ℝ), by constructor <;> nlinarith [a.2.1]⟩) ≤
        height y := by
      have h := hp.monotone (show (⟨2 * (a : ℝ), by
        constructor <;> nlinarith [a.2.1]⟩ : I) ≤ 1 by
          change 2 * (a : ℝ) ≤ 1
          linarith)
      simpa only [Path.target] using h
    have hright : height y < height (q ⟨2 * (b : ℝ) - 1, by
        constructor <;> nlinarith [b.2.2]⟩) := by
      have h := hq (show (0 : I) < ⟨2 * (b : ℝ) - 1, by
        constructor <;> nlinarith [b.2.2]⟩ by
          change 0 < 2 * (b : ℝ) - 1
          linarith)
      simpa only [Path.source] using h
    exact hleft.trans_lt hright
  · exfalso
    linarith
  · apply hq
    change 2 * (a : ℝ) - 1 < 2 * (b : ℝ) - 1
    linarith

theorem PositiveCellStep.segment_height_strictMono {n : ℕ} {G : PennyGraph n}
    {e f : OrientedEdge G} (h : PositiveCellStep e f) :
    StrictMono (fun t => cross2 (carriedVector e)
      (Path.segment (edgeCenter e) (edgeCenter f) t)) := by
  have hheight : cross2 (carriedVector e) (edgeCenter e) <
      cross2 (carriedVector e) (edgeCenter f) := by
    have hh := h.height_lt
    unfold edgeHeight at hh
    rwa [← h.to_cellStep.vector_eq] at hh
  intro a b hab
  have hab' : (a : ℝ) < b := hab
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
    cross2_add_right, cross2_smul_right]
  nlinarith [mul_pos (sub_pos.mpr hab') (sub_pos.mpr hheight)]

def positiveSpineTrace {n : ℕ} {G : PennyGraph n} (s t : OrientedEdge G) : Set Plane :=
  {z | ∃ e f : OrientedEdge G,
    Relation.ReflTransGen PositiveCellStep s e ∧ PositiveCellStep e f ∧
    Relation.ReflTransGen PositiveCellStep f t ∧
    z ∈ segment ℝ (edgeCenter e) (edgeCenter f)}

theorem positiveSpineTrace_refl {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) :
    positiveSpineTrace e e = ∅ := by
  ext z
  constructor
  · rintro ⟨a,b,hea,hab,hbe,_⟩
    exact no_closed_positive_spine e
      ((Relation.TransGen.tail' hea hab).trans_left hbe)
  · exact False.elim

theorem positiveSpineTrace_tail {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {s e f : OrientedEdge G} (hse : Relation.ReflTransGen PositiveCellStep s e)
    (hef : PositiveCellStep e f) :
    positiveSpineTrace s f = positiveSpineTrace s e ∪
      segment ℝ (edgeCenter e) (edgeCenter f) := by
  ext z
  constructor
  · rintro ⟨a,b,hsa,hab,hbf,hz⟩
    rcases hbf.cases_tail with h | ⟨c,hbc,hcf⟩
    · subst b
      have heq := positive_step_injective ht hab hef
      subst a
      exact Or.inr hz
    · have heq := positive_step_injective ht hcf hef
      subst c
      exact Or.inl ⟨a,b,hsa,hab,hbc,hz⟩
  · rintro (⟨a,b,hsa,hab,hbe,hz⟩ | hz)
    · exact ⟨a,b,hsa,hab,hbe.tail hef,hz⟩
    · exact ⟨e,f,hse,hef,Relation.ReflTransGen.refl,hz⟩

theorem positive_spine_simple_path {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {e f : OrientedEdge G} (h : Relation.TransGen PositiveCellStep e f) :
    ∃ p : Path (edgeCenter e) (edgeCenter f),
      StrictMono (fun t => cross2 (carriedVector e) (p t)) ∧
      Set.range p = positiveSpineTrace e f := by
  induction h with
  | single h =>
    refine ⟨Path.segment (edgeCenter e) (edgeCenter _), h.segment_height_strictMono, ?_⟩
    rw [Path.range_segment, positiveSpineTrace_tail ht Relation.ReflTransGen.refl h,
      positiveSpineTrace_refl, Set.empty_union]
  | @tail f g hef hfg ih =>
    obtain ⟨p,hp,hrange⟩ := ih
    let q := Path.segment (edgeCenter f) (edgeCenter g)
    have hq : StrictMono (fun t => cross2 (carriedVector e) (q t)) := by
      have hh := hfg.segment_height_strictMono
      rwa [← positive_path_vector hef.to_reflTransGen] at hh
    refine ⟨p.trans q, strictMono_height_trans p q _ hp hq, ?_⟩
    rw [Path.trans_range, hrange, Path.range_segment,
      positiveSpineTrace_tail ht hef.to_reflTransGen hfg]

theorem positive_spine_embedded_path {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {e f : OrientedEdge G} (h : Relation.TransGen PositiveCellStep e f) :
    ∃ p : Path (edgeCenter e) (edgeCenter f),
      Topology.IsClosedEmbedding p ∧ Set.range p = positiveSpineTrace e f := by
  obtain ⟨p,hp,hrange⟩ := positive_spine_simple_path ht h
  refine ⟨p, p.continuous.isClosedEmbedding ?_, hrange⟩
  intro a b hab
  exact hp.injective (congrArg (cross2 (carriedVector e)) hab)

def trackSpineTrace {n : ℕ} {G : PennyGraph n} (c : TrackComponent G) : Set Plane :=
  {z | ∃ e : OrientedEdge G, edgeComponent e = c ∧ z = edgeCenter e} ∪
  {z | ∃ e f : OrientedEdge G, edgeComponent e = c ∧ PositiveCellStep e f ∧
    z ∈ segment ℝ (edgeCenter e) (edgeCenter f)}

theorem onSpine_center_mem_trace {n : ℕ} {G : PennyGraph n}
    {s t e : OrientedEdge G} (hst : Relation.TransGen PositiveCellStep s t)
    (he : OnSpine s t e) : edgeCenter e ∈ positiveSpineTrace s t := by
  rcases he.1.cases_tail with h | ⟨a,hsa,hae⟩
  · subst e
    obtain ⟨b,hsb,hbt⟩ := Relation.TransGen.head'_iff.mp hst
    exact ⟨s,b,Relation.ReflTransGen.refl,hsb,hbt,left_mem_segment ℝ _ _⟩
  · exact ⟨a,e,hsa,hae,he.2,right_mem_segment ℝ _ _⟩

theorem onSpine_reverse_iff {n : ℕ} {G : PennyGraph n} {s t e : OrientedEdge G} :
    OnSpine (reverseEdge t) (reverseEdge s) e ↔ OnSpine s t (reverseEdge e) := by
  constructor <;> intro h <;>
    simpa only [reverseEdge_involutive] using h.reverse

theorem complete_spine_trace {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {s t : OrientedEdge G} (hs : ¬ ∃ g, PositiveCellStep g s)
    (htop : ¬ ∃ g, PositiveCellStep t g)
    (hst : Relation.TransGen PositiveCellStep s t)
    (hall : ∀ e, edgeComponent e = edgeComponent s ↔ OnUnorientedSpine s t e) :
    trackSpineTrace (edgeComponent s) = positiveSpineTrace s t := by
  ext z
  constructor
  · rintro (⟨e,he,rfl⟩ | ⟨e,f,he,hef,hz⟩)
    · rcases (hall e).mp he with h | h
      · exact onSpine_center_mem_trace hst h
      · have hmem := onSpine_center_mem_trace hst (onSpine_reverse_iff.mp h)
        simpa only [edgeCenter_reverse] using hmem
    · rcases (hall e).mp he with h | h
      · exact ⟨e,f,h.1,hef,spine_suffix_closed ht htop h.2 hef,hz⟩
      · have hrev := onSpine_reverse_iff.mp h
        refine ⟨reverseEdge f,reverseEdge e,
          spine_prefix_closed ht hs hrev.1 hef.reverse,hef.reverse,hrev.2,?_⟩
        simpa only [edgeCenter_reverse,segment_symm] using hz
  · rintro ⟨e,f,hse,hef,hft,hz⟩
    exact Or.inr ⟨e,f,(positive_path_component hse).symm,hef,hz⟩

theorem onSpine_refl_eq {n : ℕ} {G : PennyGraph n} {s e : OrientedEdge G}
    (h : OnSpine s s e) : e = s := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h.1 with he | he
  · exact he
  · exact False.elim (no_closed_positive_spine s (he.trans_left h.2))

theorem track_spine_singleton_or_embedded {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (e : OrientedEdge G) :
    (∃ z : Plane, trackSpineTrace (edgeComponent e) = {z}) ∨
    (∃ s t : OrientedEdge G, ∃ p : Path (edgeCenter s) (edgeCenter t),
      Topology.IsClosedEmbedding p ∧ Set.range p = trackSpineTrace (edgeComponent e)) := by
  obtain ⟨s,t,hs,htop,he,hall⟩ := component_spine_iff ht e
  have hsc : edgeComponent s = edgeComponent e := positive_path_component he.1
  by_cases hst : s = t
  · subst t
    have hcenters (f : OrientedEdge G) (hf : edgeComponent f = edgeComponent e) :
        edgeCenter f = edgeCenter s := by
      rcases (hall f).mp hf with h | h
      · rw [onSpine_refl_eq h]
      · have hh := onSpine_refl_eq (onSpine_reverse_iff.mp h)
        have hc := congrArg edgeCenter hh
        simpa only [edgeCenter_reverse] using hc
    left
    refine ⟨edgeCenter s,?_⟩
    ext z
    constructor
    · rintro (⟨f,hf,rfl⟩ | ⟨a,b,ha,hab,hz⟩)
      · exact hcenters f hf
      · have hb : edgeComponent b = edgeComponent e :=
          (positive_path_component (Relation.ReflTransGen.single hab)).symm.trans ha
        simpa only [hcenters a ha,hcenters b hb,segment_same,Set.mem_singleton_iff] using hz
    · intro hz
      exact Or.inl ⟨s,hsc,hz⟩
  · right
    have hpath : Relation.TransGen PositiveCellStep s t := by
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp (he.1.trans he.2) with h | h
      · exact False.elim (hst h.symm)
      · exact h
    obtain ⟨p,hp,hrange⟩ := positive_spine_embedded_path ht hpath
    refine ⟨s,t,p,hp,?_⟩
    rw [hrange,← complete_spine_trace ht hs htop hpath (fun f => by
      rw [hsc]; exact hall f),hsc]

end Swanepoel
