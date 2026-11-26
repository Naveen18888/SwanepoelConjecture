module
public import Swanepoel.RhombusTransitions
public import Mathlib.Analysis.Convex.Topology
@[expose] public section

noncomputable section
namespace Swanepoel

def PennyGraph.edgePoint {n : ℕ} (G : PennyGraph n) (a b : Fin n) (t : ℝ) : Plane :=
  (1-t) • G.point a+t • G.point b

theorem PennyGraph.edgePoint_reverse {n : ℕ} (G : PennyGraph n) (a b : Fin n) (t : ℝ) :
    G.edgePoint b a (1-t)=G.edgePoint a b t := by
  dsimp [PennyGraph.edgePoint]
  module

theorem PennyGraph.edgePoint_dist_start {n : ℕ} (G : PennyGraph n) (a b : Fin n)
    (hab : G.graph.Adj a b) {t : ℝ} (ht : 0≤t) :
    dist (G.edgePoint a b t) (G.point a)=t := by
  have he : G.edgePoint a b t-G.point a=t • (G.point b-G.point a) := by
    dsimp [PennyGraph.edgePoint]
    module
  rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
  rw [← dist_eq_norm,hab.symm.2,mul_one]

theorem PennyGraph.edgePoint_ne_vertex {n : ℕ} (G : PennyGraph n) (a b i : Fin n)
    (hab : G.graph.Adj a b) {t : ℝ} (ht0 : 0<t) (ht1 : t<1) :
    G.edgePoint a b t≠G.point i := by
  intro he
  have hd := G.edgePoint_dist_start a b hab ht0.le
  rw [he] at hd
  by_cases hi : i=a
  · rw [hi,dist_self] at hd
    linarith
  · have hs := G.separated i a hi
    linarith

theorem PennyGraph.shared_edge_intersection {n : ℕ} (G : PennyGraph n)
    (a b c : Fin n) (hab : G.graph.Adj a b) (hac : G.graph.Adj a c)
    {t s : ℝ} (ht : 0<t) (hs : 0≤s)
    (he : G.edgePoint a b t=G.edgePoint a c s) : b=c := by
  have hts : t=s := by
    have h1 := G.edgePoint_dist_start a b hab ht.le
    have h2 := G.edgePoint_dist_start a c hac hs
    rw [he] at h1
    linarith
  subst s
  have hz : t • (G.point b-G.point c)=0 := by
    have hsub := sub_eq_zero.mpr he
    dsimp [PennyGraph.edgePoint] at hsub
    calc
      t • (G.point b-G.point c)=
          ((1-t) • G.point a+t • G.point b)-((1-t) • G.point a+t • G.point c) := by module
      _ = 0 := hsub
  exact G.point_injective (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left ht.ne'))

theorem PennyGraph.interior_edge_intersection {n : ℕ} (G : PennyGraph n)
    (a b c d : Fin n) (hab : G.graph.Adj a b) (hcd : G.graph.Adj c d)
    {t s : ℝ} (ht0 : 0<t) (ht1 : t<1) (hs0 : 0≤s) (hs1 : s≤1)
    (he : G.edgePoint a b t=G.edgePoint c d s) : s(a,b)=s(c,d) := by
  by_cases hac : a=c
  · subst c
    have hbd := G.shared_edge_intersection a b d hab hcd ht0 hs0 he
    rw [hbd]
  by_cases had : a=d
  · subst d
    have he' : G.edgePoint a b t=G.edgePoint a c (1-s) := by
      rw [G.edgePoint_reverse]; exact he
    have hbc := G.shared_edge_intersection a b c hab hcd.symm ht0 (by linarith) he'
    rw [hbc]
    exact Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)
  by_cases hbc : b=c
  · subst c
    have he' : G.edgePoint b a (1-t)=G.edgePoint b d s := by
      rw [G.edgePoint_reverse]; exact he
    have had := G.shared_edge_intersection b a d hab.symm hcd (by linarith) hs0 he'
    rw [had]
    exact Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)
  by_cases hbd : b=d
  · subst d
    have he' : G.edgePoint b a (1-t)=G.edgePoint b c (1-s) := by
      rw [G.edgePoint_reverse,G.edgePoint_reverse]; exact he
    have hac := G.shared_edge_intersection b a c hab.symm hcd.symm (by linarith)
      (by linarith) he'
    rw [hac]
  exact False.elim (G.disjoint_unit_edges a b c d hab hcd hac had hbc hbd
    t s ht0.le ht1.le hs0 hs1 he)

def PennyGraph.edgeTrace {n : ℕ} (G : PennyGraph n) (a b : Fin n) : Set Plane :=
  G.edgePoint a b '' Set.Icc 0 1

def PennyGraph.openEdgeTrace {n : ℕ} (G : PennyGraph n) (a b : Fin n) : Set Plane :=
  G.edgePoint a b '' Set.Ioo 0 1

def PennyGraph.drawing {n : ℕ} (G : PennyGraph n) : Set Plane :=
  Set.range G.point ∪ ⋃ e : OrientedEdge G, G.edgeTrace e.val.1 e.val.2

theorem PennyGraph.continuous_edgePoint {n : ℕ} (G : PennyGraph n) (a b : Fin n) :
    Continuous (G.edgePoint a b) :=
  ((continuous_const.sub continuous_id).smul continuous_const).add
    (continuous_id.smul continuous_const)

theorem PennyGraph.isCompact_drawing {n : ℕ} (G : PennyGraph n) : IsCompact G.drawing := by
  apply (Set.finite_range G.point).isCompact.union
  exact isCompact_iUnion (fun e => isCompact_Icc.image (G.continuous_edgePoint e.val.1 e.val.2))

theorem PennyGraph.isClosed_drawing {n : ℕ} (G : PennyGraph n) : IsClosed G.drawing :=
  G.isCompact_drawing.isClosed

theorem PennyGraph.point_mem_drawing {n : ℕ} (G : PennyGraph n) (i : Fin n) :
    G.point i ∈ G.drawing := Or.inl ⟨i,rfl⟩

theorem PennyGraph.edgeTrace_subset_drawing {n : ℕ} (G : PennyGraph n) (a b : Fin n)
    (hab : G.graph.Adj a b) : G.edgeTrace a b ⊆ G.drawing := by
  intro z hz
  exact Or.inr (Set.mem_iUnion.mpr ⟨⟨(a,b),hab⟩,hz⟩)

theorem PennyGraph.isPreconnected_openEdgeTrace {n : ℕ} (G : PennyGraph n) (a b : Fin n) :
    IsPreconnected (G.openEdgeTrace a b) :=
  isPreconnected_Ioo.image _ (G.continuous_edgePoint a b).continuousOn

theorem PennyGraph.edgeTrace_subset_closure_openEdgeTrace {n : ℕ} (G : PennyGraph n)
    (a b : Fin n) : G.edgeTrace a b ⊆ closure (G.openEdgeTrace a b) := by
  have h := image_closure_subset_closure_image (G.continuous_edgePoint a b)
    (s := Set.Ioo (0 : ℝ) 1)
  simpa only [PennyGraph.edgeTrace,PennyGraph.openEdgeTrace,
    closure_Ioo (by norm_num : (0 : ℝ)≠1)] using h

end Swanepoel
