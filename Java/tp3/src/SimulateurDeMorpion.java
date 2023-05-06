public class SimulateurDeMorpion {

    public static void main (String[] args){

        Joueur j1 = new JoueurAleatoire(1);
        Joueur j2 = new JoueurAleatoire(2);

        JeuDeMorpion j = new JeuDeMorpion(j1, j2);

        j.jouerPartie();

    }
}
