
set SERVEROUTPUT ON;

/* EXERCICE 2 DU DS*/
    /* Question 1 */
CREATE OR REPLACE PROCEDURE affiche_comp_avion
    AS
    v_annserv NUMBER;
    v_today NUMBER;
    
BEGIN
    v_today := extract( year from sysdate);
    FOR v_comp in (SELECT * FROM COMPAGNIE ) LOOP
        dbms_output.put_line( v_comp.nomcomp || ' (' || v_comp.comp || ')');
        FOR v_avion IN (SELECT * from AVION WHERE avion.comp = v_comp.comp) LOOP
            SELECT annserv into v_annserv FROM avion where avion.nuavion = v_avion.nuavion;
            v_annserv := v_today - v_annserv ;
            IF (v_avion .nom IS NOT NULL) THEN
                dbms_output.put_line('    ' || v_avion.nom || ', ' || v_annserv || ' ans');
            ELSE
                dbms_output.put_line('    sans nom, ' || v_annserv || ' ans');
            END IF;
        END LOOP;
    
    END LOOP;

END;

/

BEGIN
 affiche_comp_avion;
END;

/* Question 2 */

-- b
set SERVEROUTPUT ON;
CREATE OR REPLACE TRIGGER tr_changecomp
BEFORE UPDATE OF comp ON pilote
    CURSOR c_pilote IS SELECT nopilote FROM affectation where pilote.nopilote = affectation.nopilote;
    v_affectation NUMBER;
    v_pilote c_pilote%rowtype;
BEGIN
        FETCH c_pilote into v_pilote 
            SELECT nopilote INTO v_affectation FROM affectation a WHERE a.nopilote = v_pilote.nopilote;
            IF (v_affectation is not null) THEN
                close c_pilote;
                raise_application_error(-20001, 'Pilote déjà affecté');
            END IF;
            close c_pilote;
END tr_changecomp;
    