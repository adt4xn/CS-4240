Require Export List.

Inductive month : Type :=
  | one: month
  | two: month.


(** This is the header data type. Headers are represented as nats  **)

Record col_header: Set := make_header {
  get_header_nat: nat
}. 

(**  column data type. it is a function from [nat] to [list nat] in which the
    nat is essentially the "header" of the column and the list is all the
    entries in that column  **)

Inductive column : Type :=  
  | make_col : col_header -> list nat -> column.


Example header1 := make_header 9.
Example header2 := make_header 4.
Example column1 := make_col header1 (4::2::89::nil).
Example column2 := make_col header2 (5::77::nil).

(** table data type. it is just a list of columns  **)
Definition table : Type : list column.

(**  database data type. Is essentially just a list of rows  **)
Definition db: Type := list table.


Inductive select (d: db)(l: list column)