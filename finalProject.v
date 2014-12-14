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


Inductive select (d: db)(l: list column)