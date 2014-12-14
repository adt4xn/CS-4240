Require Export List.
Require Export String.
Open Scope string_scope.
Open Scope list_scope.

Inductive month : Type :=
  | one: month
  | two: month.

(** This is the header data type. Headers are represented as nats  **)

Record col_header: Set := make_header {
  get_header_str: string
}. 

(**  column data type. it is a function from [nat] to [list nat] in which the
    nat is essentially the "header" of the column and the list is all the
    entries in that column  **)

Inductive column :=  
  | make_col_nat : col_header -> list nat -> column
  | make_col_string : col_header -> list string -> column.


Example header1 := make_header "id numbers".
Example header2 := make_header "names".
Example column1 := make_col_nat header1 (nil).
Example column2 := make_col_string header2 (nil).

(** table data type. it is just a list of columns  **)
Definition table := list column.

(**  database data type. Is essentially just a list of rows  **)
Definition db := list table.

Definition colinsert (dbcol : column) (X: nat) (Y: string) : column :=
 match dbcol with
 | make_col_nat header listnat => make_col_nat header (X::listnat)
 | make_col_string header liststring => make_col_string header (Y::liststring)
 end.

Fixpoint insert (dbtable sizeonetable : table) : list column := 
 match dbtable with
 | nil => dbtable
 | cons h t =>
  match h with
  | make_col_nat mainheader mainlistnat =>
   match sizeonetable with
   | nil => dbtable
   | cons oh ot => 
    match oh with
    | make_col_nat oheader olistnat =>
     match olistnat with
     | _ :: _ :: _ => dbtable
     | nil => dbtable
     | cons val nil => (colinsert h val "null")::(insert t ot)
     end
    | make_col_string oheader oliststring => dbtable
    end
   end
  | make_col_string mainheader mainliststring =>
   match sizeonetable with
   | nil => dbtable
   | cons oh ot => 
    match oh with
    | make_col_string oheader oliststring =>
     match oliststring with
     | _ :: _ :: _ => dbtable
     | nil => dbtable
     | cons val nil => (colinsert h 0 val)::(insert t ot)
     end
    | make_col_nat oheader olistnat => dbtable
    end
   end
  end
 end.
 

Inductive select (d: db)(l: list column)