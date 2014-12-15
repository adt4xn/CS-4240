(**  CS 4240 FINAL PROJECT    **)

(** Here we implement a very simple database data structure and a few SQL-like
commands to go with it. The database is simply a list of columns (which
we define). A column is a function from "header" to some list (either a list
of nats or a list of strings. For simplicity sake, we assume there are only
two possible data types for the entries of this database, nat and string). 
Thus, again, a column is just a list of all the entries in said column. 
The commands we implement are 
   1. insert - insert a row of data into the table
   2. select - select a row of data to be passed to some other function
   3. drop_row - drop a row from the table
   4. drop_column - drop a column from the table   **)

Require Export List.
Require Export String.
Open Scope string_scope.
Open Scope list_scope.
Require Import Ascii.
Require Import Arith.

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

(** table data type. it is just a list of columns  **)
Definition table := list column.


Example header1 := make_header "id numbers".
Example header2 := make_header "names".
Example column1 := make_col_nat header1 (1::2::3::nil).
Example column2 := make_col_string header2 ("John"::"Millie"::"Herbert"::nil).
Example table1 := column1::column2::nil.

(**  database data type. Is essentially just a list of rows  **)
Definition db := list table.

(** Insert into a column. If the column is a string type, the function
will attempt to insert the string parameter. If column is nat, then the nat **)
Definition colinsert (dbcol : column) (X: nat) (Y: string) : column :=
 match dbcol with
 | make_col_nat header listnat => make_col_nat header (X::listnat)
 | make_col_string header liststring => make_col_string header (Y::liststring)
 end.

Example minicolumn1 := make_col_nat header1 (4::nil).
Example minicolumn2 := make_col_string header2 ("Roxanne"::nil).
Example minitable1 := minicolumn1::minicolumn2::nil.

(** Insert a table of size one (such as minitable1, above) into a preexisting table **)
Fixpoint insert (dbtable sizeonetable : table) : table := 
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

Compute insert table1 minitable1.

(** A string equivalency function, necessary for checking names of fields against parameters, found from stack overflow **)
Fixpoint beq_str (sa sb : string) {struct sb}: bool := 
   match sa, sb with
 | EmptyString, EmptyString  => true
 | EmptyString, String b sb' => false
 | String a sa', EmptyString => false
 | String a sa', String b sb'=> match (ascii_dec a b) with 
                                | left _ => beq_str sa' sb'
                                | right _ => false
                                end
 end.

(** Takes in a table and a field name, and drops the column of the given name **)
Fixpoint dropcolumn(dbtable: table)(s: string) : table :=
  match dbtable with
  | nil => nil
  | cons h t => match h with
            | make_col_string head list =>
              if (beq_str (get_header_str head) s) then t else h::(dropcolumn t s)
            | make_col_nat hnat lnat =>
              if (beq_str (get_header_str hnat) s) then t else h::(dropcolumn t s)
end
end.

Check (get_header_str header1).
Compute (get_header_str header1).
Compute dropcolumn table1 "names".

(** A helper function for selectWhere. Finds the index of the given value among a list of nats **)
Fixpoint getNatIndex (natlist: list nat) (value: nat) (index: nat) : nat := 
  match natlist with
  | h'::t' => if (beq_nat value h') then index 
              else getNatIndex t' value (S (index))
  | nil => index
  end.

(** A helper function for selectWhere. Finds the index of the given value among a list of strings **)
Fixpoint getStringIndex (stringlist: list string) (value: string) (index: nat) : nat := 
  match stringlist with
  | h'::t' => if (beq_str value h') then index 
              else getStringIndex t' value (S (index))
  | nil => index
  end.

(** A helper function for selectWhere. Calls the two functions above to find the index of the
given value from the entire table **)
Fixpoint selectIndex (table: table)(field : string)(natval: nat)(stringval: string): nat := 
 match table with
 | cons h t => 
  match h with
  | make_col_nat natheader natlist => 
   if (beq_str (get_header_str natheader) field) 
   then getNatIndex natlist natval 0
   else selectIndex t field natval stringval 
  | make_col_string stringheader stringlist => 
   if (beq_str (get_header_str stringheader) field) 
   then getStringIndex stringlist stringval 0
   else selectIndex t field natval stringval
  end
 | nil => 0
 end.

(** A helper function for selectWhere. Returns the value, from a list of nats, at a given index. Used to help build
the return value for selectWhere **)
Fixpoint natElemAt (list: list nat) (index: nat): nat :=
 match list with
 | h::t => match index with
          | 0 => h
          | S n => natElemAt t n
          end
 | nil => 0
 end.

(** A helper function for selectWhere. Returns the value, from a list of strings, at a given index. Used to help build
the return value for selectWhere **)
Fixpoint stringElemAt (list: list string) (index: nat): string :=
 match list with
 | h::t => match index with
          | 0 => h
          | S n => stringElemAt t n
          end
 | nil => "no valid string"
 end.

Compute selectIndex table1 "id numbers" 5 "John".
Compute stringElemAt ("Bob"::"Rick"::"Matt"::nil) 1.

Compute selectIndex table1 "id numbers" 3 "test".
Compute selectIndex table1 "names" 3 "Herbert".

(** selectWhere. Takes in the full table, a second table (to recurse over), the field, a natval and a stringval. 
The function will only use one of the natval or stringval, depending on the given field's type. **)

Fixpoint selectWhere (table: table)(rec_table: list column)(field: string)(natval: nat)(stringval: string): list column := 
 match rec_table with
 | cons h t => 
  match h with
  | make_col_nat natheader natlist => 
                 make_col_nat natheader ((natElemAt natlist (selectIndex table field natval stringval))::nil)::(selectWhere table t field natval stringval)
  | make_col_string stringheader stringlist => 
                 make_col_string stringheader ((stringElemAt stringlist (selectIndex table field natval stringval))::nil)::(selectWhere table t field natval stringval)
  end
 | nil => nil
 end.

Compute selectWhere table1 table1 "id numbers" 3 "test".
(** Two of the same tables are initially passed in to the function for the following reason:
 in 'Compute selectWhere table1 table1 "id numbers" 3 "Millie"' above, we iterate over the columns in the second
table1, replacing them with columns of height=1. This changes the index of id number 3 from 2 to 0 in the resulting table, 
and thus, we would end up using the name at index 0... not the one we want. By supplying a second table to the function,
we have an unaltered reference from which we can derive the proper indicies. **)

(** helper function for the merge command that takes two columns and checks to see if
they have the same header. If they do, they will be combined into one column in the merge
function that follows **)

Definition combine_cols(c1 c2: column) : column :=
  match c1, c2 with
  | make_col_nat h1 l1, make_col_nat h2 l2 =>
        if (beq_str (get_header_str h1)(get_header_str h2)) then make_col_nat h1 (l1++l2)
        else c1
  | make_col_string h1 l1, make_col_string h2 l2 =>
        if (beq_str (get_header_str h1)(get_header_str h2)) then make_col_string h1 (l1++l2)
        else c1
  | make_col_nat _ _, make_col_string _ _ => c1
  | make_col_string _ _, make_col_nat _ _ => c1
end.

(** Merge command. Takes two tables and combines columns of the two seperate tables
 that have the same header **)

Fixpoint merge (t1 t2: table) : table :=
  match t1, t2 with
    | nil, nil => nil
    | nil, _ => t2
    | _, nil => t1
    | h::t, h'::t' => 
      match h, h' with
      | make_col_nat h1 l1, make_col_nat h2 l2 => (combine_cols h h')::(merge t t')
      | make_col_string h1 l1, make_col_string h2 l2 => (combine_cols h h')::(merge t t')
      | make_col_string _ _, make_col_nat _ _ => merge t t'
      | make_col_nat _ _, make_col_string _ _ => merge t t'
end
end.

Example table2 := column1::column2::nil.

(** This should merge the columns of table1 and table2 that have the same
headings. Thus, there will be the same number of columns in the resulting
table as the two that are being merged, but all of the data from each
table will be in one table.  **)

Compute merge table1 table2.

(** This will drop the column titled "id numbers" from table1. As a result
table1 will be left with one column, "names" **)
Compute dropcolumn table1 "id numbers".



(* adam *)





