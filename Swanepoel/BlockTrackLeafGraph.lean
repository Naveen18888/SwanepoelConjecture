module
public import Swanepoel.CyclicBlock
public import Swanepoel.Restrictions
public import Swanepoel.L38HalfPentagonEmbedding
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace PennyGraph
variable {n : ℕ} (G : PennyGraph n)

def eraseVertexSet (_G : PennyGraph n) (v : Fin n) : Finset (Fin n) := Finset.univ.erase v

def eraseVertex (v : Fin n) : PennyGraph (G.eraseVertexSet v).card := G.restrict (G.eraseVertexSet v)

@[simp] theorem mem_eraseVertexSet (v w : Fin n) : w∈G.eraseVertexSet v ↔ w≠v := by
  simp [eraseVertexSet]

def eraseVertexMap (v : Fin n) (i : Fin (G.eraseVertexSet v).card) : Fin n :=
  ((G.eraseVertexSet v).equivFin.symm i).val

theorem eraseVertexMap_injective (v : Fin n) : Function.Injective (G.eraseVertexMap v) := by
  intro i j h
  exact (G.eraseVertexSet v).equivFin.symm.injective (Subtype.ext h)

theorem eraseVertexMap_ne (v : Fin n) (i : Fin (G.eraseVertexSet v).card) : G.eraseVertexMap v i≠v :=
  (G.mem_eraseVertexSet v _).mp ((G.eraseVertexSet v).equivFin.symm i).property

def eraseVertexIndex (v w : Fin n) (hw : w≠v) : Fin (G.eraseVertexSet v).card :=
  (G.eraseVertexSet v).equivFin ⟨w,(G.mem_eraseVertexSet v w).mpr hw⟩

@[simp] theorem eraseVertexMap_index (v w : Fin n) (hw : w≠v) :
    G.eraseVertexMap v (G.eraseVertexIndex v w hw)=w :=
  congrArg Subtype.val ((G.eraseVertexSet v).equivFin.symm_apply_apply _)

@[simp] theorem eraseVertex_point (v : Fin n) (i : Fin (G.eraseVertexSet v).card) :
    (G.eraseVertex v).point i=G.point (G.eraseVertexMap v i) := rfl

def eraseVertexEmbedding (v : Fin n) : L38HalfPentagonEmbedding (G.eraseVertex v) G :=
  ⟨G.eraseVertexMap v,G.eraseVertexMap_injective v,G.eraseVertex_point v⟩

def eraseLiftEdge (v : Fin n) (e : OrientedEdge G) (ha : e.val.1≠v) (hb : e.val.2≠v) :
    OrientedEdge (G.eraseVertex v) :=
  ⟨(G.eraseVertexIndex v e.val.1 ha,G.eraseVertexIndex v e.val.2 hb),
    ((G.eraseVertexEmbedding v).adj_iff _ _).mpr (by
      change G.graph.Adj (G.eraseVertexMap v (G.eraseVertexIndex v e.val.1 ha))
        (G.eraseVertexMap v (G.eraseVertexIndex v e.val.2 hb))
      simpa only [G.eraseVertexMap_index] using e.property)⟩

@[simp] theorem eraseLiftEdge_map (v : Fin n) (e : OrientedEdge G) (ha : e.val.1≠v) (hb : e.val.2≠v) :
    (G.eraseVertexEmbedding v).mapEdge (G.eraseLiftEdge v e ha hb)=e := by
  apply Subtype.ext
  exact Prod.ext (G.eraseVertexMap_index v _ ha) (G.eraseVertexMap_index v _ hb)

theorem eraseVertex_triangleFree (ht : G.TriangleFree) (v : Fin n) : (G.eraseVertex v).TriangleFree :=
  G.restrict_triangleFree _ ht

theorem eraseVertex_card_add_one (v : Fin n) : (G.eraseVertexSet v).card+1=n := by
  simpa only [eraseVertexSet,Finset.card_univ,Fintype.card_fin] using
    Finset.card_erase_add_one (Finset.mem_univ v)

theorem eraseVertex_card_lt (v : Fin n) : (G.eraseVertexSet v).card<n := by
  have h := G.eraseVertex_card_add_one v
  omega

theorem leaf_degree_one (v a : Fin n) (ha : G.graph.Adj v a)
    (hunique : ∀ w,G.graph.Adj v w → w=a) : G.graph.degree v=1 :=
  SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr ⟨a,ha,hunique⟩

theorem eraseVertex_connected (hc : G.graph.Connected) (v a : Fin n) (ha : G.graph.Adj v a)
    (hunique : ∀ w,G.graph.Adj v w → w=a) : (G.eraseVertex v).graph.Connected := by
  have h := hc.induce_compl_singleton_of_degree_eq_one (G.leaf_degree_one v a ha hunique)
  have hset : (G.eraseVertexSet v : Set (Fin n))={v}ᶜ := by
    ext w
    simp only [Finset.mem_coe,G.mem_eraseVertexSet,Set.mem_compl_iff,Set.mem_singleton_iff]
  apply (G.restrictIso (G.eraseVertexSet v)).connected_iff.mpr
  rw [hset]
  exact h

theorem eraseVertex_edgeCount_add_one (v a : Fin n) (ha : G.graph.Adj v a)
    (hunique : ∀ w,G.graph.Adj v w → w=a) :
    (G.eraseVertex v).edgeCount+1=G.edgeCount := by
  have hdeg := G.leaf_degree_one v a ha hunique
  have hinc : (G.graph.edgeFinset.filter (fun e => v∈e)).card=1 := by
    rw [← G.graph.incidenceFinset_eq_filter,G.graph.card_incidenceFinset_eq_degree,hdeg]
  have hfilter : G.graph.edgeFinset.filter (fun e => e.toFinset⊆G.eraseVertexSet v)=
      G.graph.edgeFinset.filter (fun e => v∉e) := by
    apply Finset.filter_congr
    intro e _
    simp only [eraseVertexSet,Finset.subset_erase,Finset.subset_univ,true_and,Sym2.mem_toFinset]
  have hcount : (G.eraseVertex v).edgeCount=(G.graph.edgeFinset.filter (fun e => v∉e)).card := by
    change (G.restrict (G.eraseVertexSet v)).edgeCount=_
    rw [G.restrict_edgeCount,← G.graph.card_filter_edgeFinset_toFinset_subset,hfilter]
  have h := Finset.card_filter_add_card_filter_not (s := G.graph.edgeFinset) (p := fun e => v∈e)
  change (G.eraseVertex v).edgeCount+1=G.graph.edgeFinset.card
  omega

theorem eraseVertex_drawing_subset (v : Fin n) : (G.eraseVertex v).drawing⊆G.drawing := by
  rintro z (⟨i,rfl⟩ | hz)
  · exact G.point_mem_drawing (G.eraseVertexMap v i)
  · obtain ⟨e,he⟩ := Set.mem_iUnion.mp hz
    exact G.edgeTrace_subset_drawing _ _ ((G.eraseVertexEmbedding v).mapEdge e).property he

theorem eraseVertex_face_count (hc : G.graph.Connected) (v a : Fin n) (ha : G.graph.Adj v a)
    (hunique : ∀ w,G.graph.Adj v w → w=a) :
    Nat.card (PlaneFace G)=Nat.card (PlaneFace (G.eraseVertex v)) := by
  have hn := G.eraseVertex_card_add_one v
  have hm := G.eraseVertex_edgeCount_add_one v a ha hunique
  have heG := G.faceEuler_of_connected hc
  have heH := (G.eraseVertex v).faceEuler_of_connected (G.eraseVertex_connected hc v a ha hunique)
  change (n : ℤ)-G.edgeCount+Fintype.card (BoundedFace G)=1 at heG
  change ((G.eraseVertexSet v).card : ℤ)-(G.eraseVertex v).edgeCount+
    Fintype.card (BoundedFace (G.eraseVertex v))=1 at heH
  have hb : Fintype.card (BoundedFace G)=Fintype.card (BoundedFace (G.eraseVertex v)) := by omega
  rw [G.all_face_count,(G.eraseVertex v).all_face_count,hb]

end PennyGraph
end Swanepoel
