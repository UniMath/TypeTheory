
(** 

 Ahrens, Lumsdaine, Voevodsky, 2015–

Contents:

  - Equivalence between split type-categories and their reassociated version based on object-extension structures
*)

Require Import UniMath.Foundations.Basics.Sets.
Require Import TypeTheory.Auxiliary.CategoryTheoryImports.

Require Import TypeTheory.Auxiliary.Auxiliary.
Require Import TypeTheory.Auxiliary.UnicodeNotations.

Require Import TypeTheory.ALV1.CwF_SplitTypeCat_Defs.
Require Import TypeTheory.ALV1.TypeCat.

Section Structural_Reassoc.

Context
  (T_ty : UU)
  (T_ext : T_ty -> UU)
  (T_dpr : Π ty, T_ext ty -> UU)
  (T_reind : T_ty -> UU)
  (T_q_etc : Π ty ext, (T_dpr ty ext) -> (T_reind ty) -> UU)
  (T_set : T_ty -> UU)
  (T_reind_id : Π ty, T_reind ty -> UU)
  (T_q_id : Π ty ext dpr reind,
    (T_q_etc ty ext dpr reind) -> (T_reind_id ty reind) -> UU)
  (T_reind_comp : Π ty, T_reind ty -> UU)
  (T_q_comp : Π ty ext dpr reind, 
    (T_q_etc ty ext dpr reind) -> (T_reind_comp ty reind) -> UU).

Arguments T_dpr [_] _.
Arguments T_q_etc [_ _] _ _.
Arguments T_reind_id [_] _.
Arguments T_q_id [_ _ _ _] _ _.
Arguments T_reind_comp [_] _.
Arguments T_q_comp [_ _ _ _] _ _.

(* Parallel the way a split type-cat is built up: *)

Definition struct1 : UU
  := Σ ty (ext : T_ext ty), T_reind ty.

Definition struct2 (S1 : struct1)
  (ty := pr1 S1) (ext := pr1 (pr2 S1)) (reind := pr2 (pr2 S1))
:= Σ dpr, @T_q_etc ty ext dpr reind.

Definition struct_total := Σ S1, struct2 S1.

Definition is_split (S : struct_total)
  (ty := pr1 (pr1 S)) (reind := pr2 (pr2 (pr1 S))) (q_etc := pr2 (pr2 S))
:= T_set ty
  × (Σ reind_id, T_q_id q_etc reind_id)
  × (Σ reind_comp, T_q_comp q_etc reind_comp).

Definition split_struct := Σ S, is_split S.

(* Reassociated version, close to the version involving object-extension structures *)

Definition pshf_data
:= Σ (Ty : Σ (ty : T_ty), T_set ty), T_reind (pr1 Ty).

Definition pshf_axioms (F : pshf_data)
  (reind := pr2 F)
:= T_reind_id reind × T_reind_comp reind.

Definition pshf
:= Σ F, pshf_axioms F.

Definition ext_struct (F : pshf_data)
  (ty := pr1 (pr1 F)) (reind := pr2 F)
:= Σ (ext : T_ext ty), T_dpr ext.

Definition obj_ext_struct
:= Σ (F : pshf), ext_struct (pr1 F).

Definition gen_q_mor_data (X : obj_ext_struct)
  (ext := pr1 (pr2 X)) (dpr := pr2 (pr2 X))
  (reind := pr2 (pr1 (pr1 X))) 
:= T_q_etc dpr reind.

Definition gen_q_mor_axs {X : obj_ext_struct} (q_etc : gen_q_mor_data X)
  (A := pr2 (pr1 X)) (reind_id := pr1 A) (reind_comp := pr2 A)
:= T_q_id q_etc reind_id × T_q_comp q_etc reind_comp.

Definition gen_q_mor_struct (X : obj_ext_struct)
:= Σ (q_etc : gen_q_mor_data X), gen_q_mor_axs q_etc.

Definition reassoc_split_struct
:= Σ X, gen_q_mor_struct X.


(* Timing test *)

(*
Definition temp : reassoc_split_struct -> reassoc_split_struct.
Proof.
Time intros [[[[[ty set] reind] [reind_id reind_comp]] [ext dpr]] [q_etc [q_id q_comp]]].
Abort.

Definition temp : split_struct -> split_struct.
Proof.
  Time intros [[[ty [ext reind]] [dpr q_etc]] [set [[reind_id q_id] [reind_comp q_comp]]]].
Abort.
*)

(* Equivalence between original and reassociated versions *)

Definition l_to_r_reassoc_direct : split_struct -> reassoc_split_struct.
Proof.
    intros S.
    mkpair.
      mkpair.
        exists ((pr1 (pr1 (pr1 S)),, pr1 (pr2 S)),, pr2 (pr2 (pr1 (pr1 S)))).
        exact (pr1 (pr1 (pr2 (pr2 S))),, pr1 (pr2 (pr2 (pr2 S)))).
      exact (pr1 (pr2 (pr1 (pr1 S))),, pr1 (pr2 (pr1 S))).
    exists (pr2 (pr2 (pr1 S))).
    cbn.
    exact (pr2 (pr1 (pr2 (pr2 S))),, pr2 (pr2 (pr2 (pr2 S)))).
Time Defined.

Definition r_to_l_reassoc_direct : reassoc_split_struct -> split_struct.
Proof.
  intros S.
  mkpair.
    exists (pr1 (pr1 (pr1 (pr1 (pr1 S)))) ,,
                (pr1 (pr2 (pr1 S)) ,, (pr2 (pr1 (pr1 (pr1 S)))))).
    exact (pr2 (pr2 (pr1 S)),, pr1 (pr2 S)).
  Time repeat apply dirprodpair; simpl.
  - exact (pr2 (pr1 (pr1 (pr1 (pr1 S))))).
  - exact (pr1 (pr2 (pr1 (pr1 S))),, pr1 (pr2 (pr2 S))).
  - exact (pr2 (pr2 (pr1 (pr1 S))),, pr2 (pr2 (pr2 S))).
Time Defined.

Theorem weq_reassoc_direct : split_struct ≃ reassoc_split_struct.
Proof.
  refine (weqgradth
            l_to_r_reassoc_direct
            r_to_l_reassoc_direct
            _ _).
  - Time intros [[[ty [ext reind]] [dpr q_etc]] [set [[reind_id q_id] [reind_comp q_comp]]]].
    apply idpath.
  - Time intros [[[[[ty set] reind] [reind_id reind_comp]] [ext dpr]] [q_etc [q_id q_comp]]].
    apply idpath.
Time Defined.

End Structural_Reassoc.



(** ** Equivalence between actual split type cats and their abstracted version *)

Section Split_Type_Cat_as_Structural.

Context {CC : Precategory}.

Definition T_ty
  := (CC -> UU).
Definition T_ext
  := (λ ty, Π Γ : CC, ty Γ -> CC).
Definition T_dpr
  := (λ ty ext, Π (Γ : CC) (A : ty Γ), ext Γ A --> Γ ).
Definition T_reind
  := (λ ty, Π (Γ : CC) (A : ty Γ) (Γ' : CC), (Γ' --> Γ) -> ty Γ').
Definition T_q_etc
  := (λ ty ext (dpr : T_dpr ty ext) (reind : T_reind ty), 
     Σ (q : Π (Γ:CC) (A : ty Γ) Γ' (f : Γ' --> Γ),
         (ext Γ' (reind _ A _ f)) --> (ext Γ A))
       (dpr_q : Π Γ (A : ty Γ) Γ' (f : Γ' --> Γ),
         q _ A _ f ;; dpr Γ A = dpr Γ' (reind _ A _ f) ;; f),
       (Π Γ (A : ty Γ) Γ' (f : Γ' --> Γ),
         isPullback _ _ _ _ (dpr_q _ A _ f))).
Definition T_set
  := (λ ty : T_ty, Π Γ, isaset (ty Γ)).
Definition T_reind_id
  := (λ ty (reind : T_reind ty), Π Γ A, reind _ A _ (identity Γ) = A).
Definition T_q_id
  := (λ ty ext dpr reind (q_etc : T_q_etc ty ext dpr reind)
                         (reind_id : T_reind_id ty reind),
       Π Γ A, (pr1 q_etc) _ A _ (identity Γ)
              = idtoiso (maponpaths (ext Γ) (reind_id Γ A))).
Definition T_reind_comp
  := (λ ty (reind : T_reind ty),
       Π Γ A Γ' (f : Γ' --> Γ) Γ'' (g : Γ'' --> Γ'),
         reind _ A _ (g ;; f) = reind _ (reind _ A _ f) _ g).
Definition T_q_comp
  := (λ ty ext dpr reind (q_etc : T_q_etc ty ext dpr reind)
                         (reind_comp : T_reind_comp ty reind),
       Π Γ A Γ' (f : Γ' --> Γ) Γ'' (g : Γ'' --> Γ'),
         (pr1 q_etc) _ A _ (g ;; f)
         = idtoiso (maponpaths (ext Γ'') (reind_comp _ A _ f _ g))
               ;; (pr1 q_etc) _ (reind _ A _ f) _ g
               ;; (pr1 q_etc) _ A _ f).

Definition eq_standalone_structural
  : split_type_struct CC
    = split_struct
        T_ty T_ext T_dpr T_reind T_q_etc
        T_set T_reind_id T_q_id T_reind_comp T_q_comp.
Proof.
  Time apply idpath.
Time Defined.

Definition weq_standalone_structural
  : split_type_struct CC
    ≃ split_struct
        T_ty T_ext T_dpr T_reind T_q_etc
        T_set T_reind_id T_q_id T_reind_comp T_q_comp.
Proof.
  apply eqweqmap, eq_standalone_structural.
Defined.

(** Alternate construction of [weq_standalone_structural], retained in case it gives better computational behaviour: *)

Definition standalone_to_structural
  : split_type_struct CC
    -> split_struct
        T_ty T_ext T_dpr T_reind T_q_etc
        T_set T_reind_id T_q_id T_reind_comp T_q_comp.
Proof.
  intros S. exact (transportf (fun X => X) eq_standalone_structural S).
Defined.

Definition structural_to_standalone
  : split_struct
        T_ty T_ext T_dpr T_reind T_q_etc
        T_set T_reind_id T_q_id T_reind_comp T_q_comp
  -> split_type_struct CC.
Proof.
  intros S. exact (transportb (fun X => X) eq_standalone_structural S).
Defined.

Definition weq_standalone_structural_explicit
  : split_type_struct CC
    ≃ split_struct
        T_ty T_ext T_dpr T_reind T_q_etc
        T_set T_reind_id T_q_id T_reind_comp T_q_comp.
Proof.
  refine (weqgradth
            standalone_to_structural
            structural_to_standalone
            _ _).
  - intros; apply idpath.
  - intros; apply idpath.
Defined.

End Split_Type_Cat_as_Structural.

(* TODO:

- give weak equivalence between the second association of the abstracted version, and the imported version using object-extension structures *)




