theory SimplyTypedLambdaCalculus

imports Main

begin

type_synonym var = string

datatype type = TUnit
  | TApp type type ("_ \<rightarrow> _")

datatype expr =
    Unit
  | Var var
  | Abs var type expr
  | App expr expr
  | Let var expr expr

type_synonym ctx = "(var \<times> type) set"

inductive "value" :: "expr \<Rightarrow> bool" where
  Unit: "value Unit"
| Fn: "value (Abs x t e1)"

declare value.intros[simp,intro]

fun fvs :: "expr \<Rightarrow> var set" where
  "fvs Unit          = {}" |
  "fvs (Var v)       = {v}" |
  "fvs (Abs v ty e)  = fvs e - {v}" |
  "fvs (App e1 e2)   = fvs e1 \<union> fvs e2" |
  "fvs (Let x e1 e2) = (fvs e1 \<union> fvs e2) - {x}"

fun subst :: "var \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" where
  "subst x t Unit         = Unit" |
  "subst x t (Var v)      = (if x = v then t else Var v)" |
  "subst x t (Abs v ty e) = Abs v ty (if x = v then e else subst x t e)" |
  "subst x t (App e1 e2)  = App (subst x t e1) (subst x t e2)" |
  "subst x t (Let v t' e) = Let v (if x = v then t' else subst x t t') (if x = v then e else subst x t e)"

inductive reduce :: "expr \<Rightarrow> expr \<Rightarrow> bool" where
  CApp1: "reduce e1 e1' \<Longrightarrow> reduce (App e1 e2) (App e1' e2)"
| CApp2: "value e1      \<Longrightarrow> reduce e2 e2' \<Longrightarrow> reduce (App e1 e2) (App e1 e2')"
| RApp:  "value e2      \<Longrightarrow> reduce (App (Abs x ty e1) e2) (subst x e2 e1)"
| CLet:  "reduce e1 e1' \<Longrightarrow> reduce (Let x e1 e2) (Let x e1' e2)"
| RLet:  "value e1      \<Longrightarrow> reduce (Let x e1 e2) (subst x e1 e2)"

declare reduce.intros[simp,intro]

inductive_cases ReduceAppE[elim]: "reduce (App e1 e2) e"
inductive_cases ReduceElimE[elim]: "reduce (Let x e1 e2) e"

inductive has_type :: "ctx \<Rightarrow> expr \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ : _" [40,40,40]) where
  TypeUnit: "\<Gamma> \<turnstile> Unit : TUnit" |
  TypeVar:  "(x, \<tau>) \<in> \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> (Var x) : \<tau>" |
  TypeFn:   "\<lbrakk> (insert (x, \<tau>) \<Gamma>) \<turnstile> e : \<tau>' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Abs x \<tau> e) : (\<tau> \<rightarrow> \<tau>')" |
  TypeApp:  "\<lbrakk> \<Gamma> \<turnstile> e1 : (\<tau>' \<rightarrow> \<tau>); \<Gamma> \<turnstile> e2 : \<tau>' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (App e1 e2) : \<tau>" |
  TypeLet:  "\<lbrakk> \<Gamma> \<turnstile> e1 : \<tau>\<^sub>1; (insert (x, \<tau>\<^sub>1) \<Gamma>) \<turnstile> e2 : \<tau>\<^sub>2 \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> (Let x e1 e2) : \<tau>\<^sub>2"

declare has_type.intros[simp,intro]

inductive_cases TypeUnitE[elim!]: "\<Gamma> \<turnstile> Unit : \<tau>"
inductive_cases TypeVarE[elim!]:  "\<Gamma> \<turnstile> (Var x) : \<tau>"
inductive_cases TypeFnE[elim]:    "\<Gamma> \<turnstile> (Abs x \<tau> e) : \<tau>"
inductive_cases TypeAppE[elim]:   "\<Gamma> \<turnstile> (App e1 e2) : \<tau>"
inductive_cases TypeLet[elim]:    "\<Gamma> \<turnstile> (Let x e1 e2) : \<tau>"

inductive step_or_value where
  IsValue: "value e \<Longrightarrow> step_or_value e" |
  IsStep: "\<exists>e'. reduce e e' \<Longrightarrow> step_or_value e"

declare step_or_value.intros[simp,intro]

inductive_cases StepOrValueE[elim!]: "step_or_value e"

lemma subst_identity[simp]:
  "subst x (Var x) e = e"
  by (induct e, auto)

lemma identity_exists:
  "value e \<Longrightarrow> reduce (App (Abs x \<tau> (Var x)) e) e"
  (* found by sledgehammer *)
  by (metis RApp subst.simps(2))

theorem progress:
  "{} \<turnstile> e : \<tau> \<Longrightarrow> step_or_value e"
proof (induction  "{} :: (var \<times> type) set" "e" "\<tau>" rule:has_type.induct)
  case (TypeApp e1 \<tau>' \<tau> e2)
  then show ?case
    (* found by sledgehammer *)
    by (metis CApp1 CApp2 IsStep RApp StepOrValueE TypeUnitE type.distinct(1) value.simps)
qed blast+

lemma subst_preservation:
  "(insert (x, \<tau>') \<Gamma>) \<turnstile> e2 : \<tau> \<Longrightarrow> {} \<turnstile> e1 : \<tau>' \<Longrightarrow> \<Gamma> \<turnstile> subst x e1 e2 : \<tau>"
  sorry

theorem preservation:
  "reduce e e' \<Longrightarrow> {} \<turnstile> e : \<tau> \<Longrightarrow> {} \<turnstile> e' : \<tau>"
proof (induct arbitrary: \<tau> rule:reduce.induct)
  case (RApp e2 x \<tau>' e)
  from RApp.prems RApp.hyps show ?case
    by (induct "{} :: ctx" "App (Abs x \<tau>' e) e2" "\<tau>")
       (metis TypeFnE TypeVar dual_order.refl insert_subset subst.simps(2) subst_preservation)
next
  case (RLet e1 x e2)
  then show ?case
    by (auto simp: subst_preservation)
qed blast+



end