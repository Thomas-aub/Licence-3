import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class Plateau {
    private int longueur, largeur;
    private int[][] etatIdPlateau ;

    List<int[]> casesLibres = new ArrayList<int[]>();


    public Plateau(int _longueur, int _largeur) {
        this.longueur = _longueur;
        this.largeur = _largeur;
        this.etatIdPlateau = new int[_largeur][_longueur];

        int[] tmp;
        for (int i = 0; i < this.largeur; i++){
            for (int j = 0; j < this.longueur; j++) {

                this.casesLibres.add(new int[] {i,j});
            }
        }

        initialiser();

    }

    public List<int[]> getCasesLibres() {
        return casesLibres;
    }

    public void setCasesLibres(List<int[]> casesLibres) {
        this.casesLibres = casesLibres;
    }

    public void initialiser(){

        for (int i = 0; i < this.largeur; i++){
            for (int j = 0; j < this.longueur; j++) {
                this.etatIdPlateau[i][j] = 0;
            }
        }
    }


    public void appliquerCoup(Coup coup, int id){
        etatIdPlateau[coup.getY()][coup.getX()] = id;
    }

    public int[][] getEtatIdPlateau() {
        return etatIdPlateau;
    }

    @Override
    public String toString() {
        String tmp = "";
        for (int i = 0; i < this.largeur; i++){
            for (int j = 0; j < this.longueur; j++) {
                tmp = tmp + etatIdPlateau[i][j] + "\t";
            }
            tmp = tmp +'\n';
        }
        return tmp;
    }
}
