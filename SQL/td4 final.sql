drop table reservation;
/* ENTRAINEMENT DS TP4 */

CREATE TABLE tabl 
(
    numT number,
    nbPlaces number
); 
alter table tabl add primary key(numT);

CREATE TABLE reservation
(
  numR number primary key,
  name varchar(30), 
  heure number check(heure>10 and heure<23), 
  nbPersonnes number, 
  numT number,
  constraint fk_res_tab FOREIGN KEY(numT) references tabl(numT)
);

insert into tabl values (1, 5);
insert into tabl values (2, 10);
insert into tabl values (3, 2);

insert into reservation values(2453, 'Tom', 19, 5, 1);

/* Exercice 1 */

Create or replace view tablebloquee (numT, heure) as
(select numT, heure - 1 from reservation)
UNION
(SELECT numT, heure from reservation) 
UNION
(SELECT numT, heure + 1 from reservation);

select * from tablebloquee;



/* Exercice 2 */

Set SERVEROUTPUT ON;
CREATE OR REPLACE FUNCTION getTable (hr NUMBER, ns NUMBER)
RETURN NUMBER
AS
    nbr NUMBER := -1;
    nbp NUMBER;
    CURSOR ctabl IS (SELECT numT FROM Tabl )
                MINUS(SELECT numT FROM tablebloquee WHERE hr = heure);
BEGIN
    FOR v_tabl IN ctabl LOOP
        SELECT nbPlaces INTO nbp FROM tabl r
                WHERE v_tabl.numt = r.numT;
            IF ns <= nbp THEN
                nbr := v_tabl.numt;
            END IF;  
    END LOOP;
    RETURN nbr;
    
END getTable;

----- Le code marche mais on peut pas order by nbPlaces 


/* EXERCICE 2 CORRECTION (Avec le ORDER BY) */
Set SERVEROUTPUT ON;
CREATE OR REPLACE FUNCTION getTable (hr NUMBER, ns NUMBER)
RETURN NUMBER
AS
    nbr NUMBER;
    CURSOR c_numTable IS (SELECT numT INTO nbr FROM tabl 
        WHERE nbPlaces >= ns
        AND numT NOT IN
            (SELECT numT FROM tablebloquee
            WHERE heure = hr)
        ORDER BY nbPlaces ;)
BEGIN
    OPEN c_numTable FETCH
        FETCH ------------------------------------------ C EST DU CACA IL FAUT TOUT REPRENDRE ( RETURN PLS VALEURS)
    CLOSE;
    IF nbr IS NULL THEN
         nbr := -1;
    END IF;
    RETURN nbr;
END getTable;



------ TEST 

select getTable(10, 9) from dual;

begin
    dbms_output.put_line(getTable(19,1));
    dbms_output.put_line(getTable(19,30));
end;


/* EXERCICE 3 */

CREATE OR REPLACE TRIGGER tr_reservation
    BEFORE INSERT ON reservation
    FOR EACH ROW
DECLARE 
    v_numT reservation.numT%TYPE := getTable(:new.heure, :new.nbPersonnes);
BEGIN
    IF v_numT != -1 THEN
        :new.numT := v_numT;
        dbms_output.put_line(v_numT);
    ELSE
        raise_application_error (-20001, 'Aucune table disponible');
    END IF;
END tr_reservation;




--- test trigger

insert into reservation
values (9, 'tuto', 13, 1, null); -- reservation inseree avec numT=3
insert into reservation
values(2,'toto', 19, 30, null); -- reservation empechee pas de table dispo affiché

