import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class JeuDeMorpion {

    private Plateau plateau;
    private Joueur joueur1, joueur2;
    private int idAactualJoueur;
    List<List<int[]>> coupsGagnants = new ArrayList<>();


    public JeuDeMorpion(Joueur _joueur1, Joueur _joueur2) {
        this.joueur1 = _joueur1;
        this.joueur2 = _joueur2;
        this.plateau = new Plateau(3, 3);
        this.idAactualJoueur = _joueur1.getId();
        defCoupGagnant();

    }

    public Joueur jouerPartie() {
        Joueur retour = null; // utilisé comme variable de parcours,et renvoyé comme étant le joueur gagnant
        int cmp = 0;
        Coup c = null;
        while (!partieTerminee()) {
            retour = getJoueurSuivant();

            c = retour.getCoup(plateau);

            while (!coupPossible(c)) {
                c = retour.getCoup(this.plateau);
            }


            plateau.appliquerCoup(c, retour.getId());

            int[] tmp = new int[] {c.getX(),c.getY()};
            retour.addCoupJoue(c);

            List<int[]> newCasesLibres = plateau.getCasesLibres();
            for (int i = 0; i < plateau.getCasesLibres().size(); i++){
                if (plateau.getCasesLibres().get(i)[0] == c.getX() && plateau.getCasesLibres().get(i)[1] == c.getY()){
                    newCasesLibres.remove(i);
                }
            }

            System.out.println(plateau);

        }
        return retour;
    }

    public boolean coupPossible(Coup c){
        boolean val = false;
        for (int i = 0; i < plateau.getCasesLibres().size(); i++){
            if (plateau.getCasesLibres().get(i)[0] == c.getX() && plateau.getCasesLibres().get(i)[1] == c.getY()){
                val = true;
            }
        }


        return val;
    }

    public Joueur getJoueurSuivant(){
        if (this.idAactualJoueur == joueur1.getId()){
            this.idAactualJoueur = joueur2.getId();
            return joueur1;
        } else{
            this.idAactualJoueur = joueur1.getId();
            return joueur2;
        }

    }

    public boolean partieTerminee(){
        return (plateau.getCasesLibres().size() == 0 || gagner(joueur1) || gagner(joueur2));
    }

    private boolean partieGagnee() {
        // Vérifie si un joueur en alignant une ligne ou une colonne.
        boolean colAlignee,
                ligAlignee;
        for (int i = 0; i < LONGUEUR; ++i) {
            colAlignee = plateau.getEtatIdCase(i, 0) != 0;
            ligAlignee = plateau.getEtatIdCase(0, i) != 0;

            for (int j = 1; j < LARGEUR; ++j) {
                colAlignee = colAlignee && (plateau.getEtatIdCase(i, 0)
                        == plateau.getEtatIdCase(i, j));
                ligAlignee = ligAlignee && (plateau.getEtatIdCase(0, i)
                        == plateau.getEtatIdCase(j, i));
            }

            if (colAlignee || ligAlignee) {
                return true;
            }
        }

        // Vérifie si un joueur a gagné en alignant une diagonale.
        boolean diag1Alignee = plateau.getEtatIdCase(0, 0) != 0;
        boolean diag2Alignee = plateau.getEtatIdCase(0, LONGUEUR-1) != 0;
        for (int i = 0; i < LONGUEUR; ++i) {
            diag1Alignee = diag1Alignee && (plateau.getEtatIdCase(0, 0)
                    == plateau.getEtatIdCase(i, i));
            diag2Alignee = diag2Alignee && (plateau.getEtatIdCase(0, LONGUEUR-1)
                    == plateau.getEtatIdCase(i, LONGUEUR-1-i));
        }
        if (diag1Alignee || diag2Alignee) {
            return true;
        }
        return false;
    }


//    public boolean gagner(Joueur joueur){
//        List<int[]> test = new ArrayList<int[]>();
//        List<List<int[]> possibleWin = new ArrayList<int[]>();
//        int i = 0;
//        int j, k;
//        boolean cherche = false;
//        while (i < joueur.getCoupJoue().size() && !cherche) {
//            j = i;
//            while (j < joueur.getCoupJoue().size() && !cherche){
//                test = new ArrayList<int[]>();
//                test.add(joueur.getCoupJoue().get(joueur.getCoupJoue().size()-1));
//                test.add(joueur.getCoupJoue().get(i));
//                test.add(joueur.getCoupJoue().get(j));
//
//
//                j++;
//            }
//            i++;
//        }
//        System.out.println("VICTOIRE : " + cherche);
//        return cherche;
//    }


    public void defCoupGagnant() {
        List<int[]> col = new ArrayList<int[]>();
        List<int[]> lin = new ArrayList<int[]>();
        for (int i = 0; i < 3; i++) {
            col = new ArrayList<int[]>();
            lin = new ArrayList<int[]>();
            for (int j = 0; j < 3; j++) {
                lin.add(new int[]{i, j});
                col.add(new int[]{j, i});
            }
            this.coupsGagnants.add(col);
            this.coupsGagnants.add(lin);
        }

        List<int[]> diag = new ArrayList<int[]>();
        diag.add(new int[]{0, 0});
        diag.add(new int[]{1, 1});
        diag.add(new int[]{2, 2});
        this.coupsGagnants.add(diag);

        diag = new ArrayList<int[]>();
        diag.add(new int[]{0, 2});
        diag.add(new int[]{1, 1});
        diag.add(new int[]{2, 0});
        this.coupsGagnants.add(diag);

    }

}
