/*
 * Created on Nov 6, 2004
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package net.sf.bddbddb.order;

import java.util.Arrays;
import java.util.Random;

import jwutil.util.Assert;
import weka.classifiers.Classifier;
import weka.core.Instance;
import weka.core.Instances;
import weka.core.NoSupportForMissingValuesException;
import weka.core.Utils;

/**
 * @author Administrator
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class BaggedId3 extends Classifier {

    public final static int NUM_TREES = 10;
    MyId3 [] trees;
    double [] weights;
    Random random = new Random(System.currentTimeMillis());
    int numClasses;
    Instances origData;
    public BaggedId3(){
        trees = new MyId3[NUM_TREES];
        weights = new double[NUM_TREES];
        Arrays.fill(weights,1); //trees weight equally
    }
    
    public void setWeights(double [] weights){
        this.weights = weights;
    }
    
    public void setWeight(int index, double value){
        weights[index] = value;
    }
    /* (non-Javadoc)
     * @see weka.classifiers.Classifier#buildClassifier(weka.core.Instances)
     */
    public void buildClassifier(Instances data) throws Exception {
        numClasses = data.classAttribute().numValues();
        for(int i = 0; i < NUM_TREES; ++i){
         Instances newData = data.resample(random);  //random sample with replacement
         trees[i] = new MyId3();
         trees[i].buildClassifier(newData);
        }
        origData = data;
    }
    
    public double classifyInstance(Instance instance){
        double[] votes = new double[numClasses];
        for(int i = 0; i < NUM_TREES; ++i){
            double vote = trees[i].classifyInstance(instance);
            votes[(int) vote] += weights[i]; 
        }
        return Utils.maxIndex(votes); //simple majority
    }

    public double[] distributionForInstance(Instance instance) throws NoSupportForMissingValuesException{
        double sum = 0;
        double [] distribution = new double[numClasses];
        for(int i = 0; i < NUM_TREES; ++i){
            double [] treeDist = trees[i].distributionForInstance(instance);
            for(int j = 0; j <numClasses; ++j){
                distribution[j]+= treeDist[j] * weights[i];
            }
            sum += weights[i];
        }
        Assert._assert(sum != 0, "Sum of Weights is zero");
        for(int i = 0; i < NUM_TREES; ++i)
            distribution[i] /= sum;
        
        return distribution;
    }
    
    public Instances getOriginalData(){ return origData; }
     
}
