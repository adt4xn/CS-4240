(**  CS 4240 FINAL PROJECT    **)

(** Here we implement a very simple database data structure and a few SQL-like
commands to go with it. The database is simply a list of columns (which
we define). A column is a function from "header" to some list (either a list
of nats or a list of strings. For simplicity sake, we assume there are only
two possible data types for the entries of this database, nat and string). 
Thus, again, a column is just a list of all the entries in said column. 
The commands we implement are 
   1. insert - insert a row of data into the table
   2. select - select a row or column of data to be passed to some other function
   3. drop_row - drop a row from the table
   4. drop_column - drop a column from the table   **)

Require Export List.
Require Export String.
Open Scope string_scope.
Open Scope list_scope.
Require Import Ascii.
Require Import Arith.


(** This is the header data type. All headers are represented as strings **)
Record col_header: Set := make_header {
get_header_str: string
}.



(** column data type. it is a function from [nat] to [list nat] in which the
nat is essentially the "header" of the column and the list is all the
entries in that column **)
Inductive column :=
| make_col_nat : col_header -> list nat -> column
| make_col_string : col_header -> list string -> column.

(** table data type. it is just a list of columns **)
Definition table := list column.

Example header1 := make_header "id numbers".
Example header2 := make_header "names".
Example column1 := make_col_nat header1 (nil).
Example column2 := make_col_string header2 (nil).
Example table1 := column1::column2::nil.
Example table2 := column2::nil.


(** database data type. Is essentially just a list of rows **)
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

Compute insert table1 table2.

Fixpoint beq_str (sa sb : String.string) {struct sb}: bool := 
   match sa, sb with
 | EmptyString, EmptyString  => true
 | EmptyString, String b sb' => false
 | String a sa', EmptyString => false
 | String a sa', String b sb'=> match (ascii_dec a b) with 
                                | left _ => beq_str sa' sb'
                                | right _ => false
                                end
 end.


Fixpoint dropcolumn(dbtable: table)(s: string) : table :=
  match dbtable with
  | nil => nil
  | h::t => match h with
            | make_col_string head list =>
              if (beq_str (get_header_str head) s) then t else dropcolumn t s
            | make_col_nat h l =>
              if (beq_str (get_header_str h) s) then t else dropcolumn t s
end
end.




