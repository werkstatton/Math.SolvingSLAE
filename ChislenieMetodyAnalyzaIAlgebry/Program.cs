using System;
using System.Collections.Generic;
using System.Linq;
using System.IO;
using System.Text;
using System.Text.RegularExpressions;
namespace Algorithms
{
    internal abstract class Maths
    {
        /// <summary>
        /// Метод Гаусса (Решение СЛАУ)
        /// </summary>
        /// <param name="matrix">Начальная матрица</param>
        /// <returns></returns>
        private static double[] Gauss(double[,] matrix)
        {
            int n = matrix.GetLength(0); //Размерность
            double[,] matrixClone = new double[n, n + 1];
            for (var i = 0; i < n; i++)
                for (var j = 0; j < n + 1; j++)
                    matrixClone[i, j] = matrix[i, j];

            // Прямой ход
            for (var k = 0; k < n; k++) //k-номер строки
            {
                for (var i = 0; i < n + 1; i++)//i-номер столбца
                {
                    var c = (((i-1)!=-1)||(i+1)>=(n))?(i-1):(i+1);
                   if(matrix[k,k]==0)
                   {
                       double[] temp = new double[n];
                       for(int r=0;r<n;r++)
                       {
                           temp[r] = matrixClone[r,i];
                           matrixClone[r, i] = matrixClone[r, c];
                           matrixClone[r, c] = temp[r];
                           for (var y = 0; y < n; y++) //Обновление
                           for (var j = 0; j < n + 1; j++)
                               matrix[y, j] = matrixClone[y, j];

                       }
                       matrixClone[k, i] = matrixClone[k, i] / matrixClone[k, k]; //Деление k-строки на первый член
                   }
                   else {
                       matrixClone[k, i] = matrixClone[k, i] / matrix[k, k]; //Деление k-строки на первый член
                   }

                }

                for (int i = k + 1; i < n; i++) //i-номер следующей строки после k
                {
                    double conf = matrixClone[i, k] / matrixClone[k, k]; //Коэффициент
                    for (int j = 0; j < n + 1; j++) //j-номер столбца следующей строки после k
                        matrixClone[i, j] = matrixClone[i, j] - matrixClone[k, j] * conf; //Зануление элементов матрицы ниже первого члена, преобразованного в единицу
                }
                for (int i = 0; i < n; i++) //Обновление
                    for (int j = 0; j < n + 1; j++)
                        matrix[i, j] = matrixClone[i, j];
            }

            // Обратный ход
            for (int k = n - 1; k > -1; k--) //k-номер строки
            {
                for (int i = n; i > -1; i--) //i-номер столбца
                {
                  matrixClone[k, i] = matrixClone[k, i] / matrix[k, k];
                }

                for (int i = k - 1; i > -1; i--) //i-номер следующей строки после k
                {
                    double conf = matrixClone[i, k] / matrixClone[k, k];
                    for (int j = n; j > -1; j--) //j-номер столбца следующей строки после k
                        matrixClone[i, j] = matrixClone[i, j] - matrixClone[k, j] * conf;
                }
            }

            // Отделяем от общей матрицы ответы
            double[] answer = new double[n];
            for (int i = 0; i < n; i++)
                answer[i] = matrixClone[i, n];

            return answer;
        }

        private static double[] Thomas(double[,] matrix)
        {
          var n = matrix.GetLength(0); //Размерность
          if( n+1 != matrix.GetLength(1)) //Условие размерности
          {
              Console.WriteLine("Array doesn't fit to this method");
              return null;
          }
          var matrixA = new double[n, n];
          for (var i = 0; i < n; i++)
              for (var j = 0; j < n; j++)
                  matrixA[i, j] = matrix[i, j];

          var matrixB = new double[n];
            for (var i = 0; i < n; i++)
              matrixB[i]=matrix[i,n];

          for(var i=1;i<n-1;i++)
          {
            for(var j=1;j<n-1;j++)
            {
              if(matrixA[i,i] < Math.Abs(matrixA[i,i-1])+Math.Abs(matrixA[i,i+1]))
              {
                Console.WriteLine("Array doesn't fit to this method");
                Fill(matrixB,0);
                return matrixB;
              }
              if(matrixA[i,i]==0)
              {
                Console.WriteLine("Array doesn't fit to this method");
                Fill(matrixB,0);
                return matrixB;
              }
            }
          }

          var u = new double[n];
          var v = new double[n];

          //Первая строка матрицы
          v[0] = matrixA[0,1]/(-matrixA[0,0]);
          u[0] = -matrixB[0]/(-matrixA[0,0]);

          //После первой до n-1 строки матрицы
          for(int i=1; i<n-1;i++)
          {
            v[i]= matrixA[i,i+1]/(-matrixA[i,i]-matrixA[i,i-1]*v[i-1]);
            u[i]= (matrixA[i,i-1]*u[i-1]-matrixB[i])/(-matrixA[i,i]-matrixA[i,i-1]*v[i-1]);
          }
          //Последняя строка матрицы
          v[n-1]=0;
          u[n-1]=(matrixA[n-1,n-2]*u[n-2]-matrixB[n-1])/(-matrixA[n-1,n-1]-matrixA[n-1,n-2]*v[n-2]);


                  // Отделяем от общей матрицы ответы
                  var answer = new double[n];
                  answer[n-1]=u[n-1];
                  for (var i = n-1; i > 0; i--)
                      answer[i-1] =v[i-1]*answer[i]+u[i-1];

                  return answer;
        }

        public static double SinTailor(int a, double n)
        {
          double result=0;
          for(var i=0; i<a; i++)
          {
            result += (Math.Pow(-1,i)*Math.Pow(n,(2*i+1)))/Factorial(2*i+1);
          }
          return result;
        }

        private static int Factorial(int n)
        {
            if (n == 1) return 1;

            return n * Factorial(n - 1);
        }

        private static double[] Iteration(double[,] matrix, double e)
        {
          var n = matrix.GetLength(0); //Строки
          var m = matrix.GetLength(1); //Столбцы + В
          
          var sumOfLine = new double[n];
          Fill(sumOfLine,0);
          for(var i=0;i<n;i++)
            for(var j=0;j<m-1;j++)
              sumOfLine[i] += matrix[i,j]; //Сумма элементов для каждой строки

          for(var i=0;i<n;i++)
          {
              var lineOfMatrix = new double[m - 1];
              for (var j = 0; j < m - 1; j++)
                  lineOfMatrix[j] = Math.Abs(matrix[i, j]); //Копируем абсолютные значения элементов i-ой строки
              
              var maxNum = lineOfMatrix.Max(); //Получаем элемент i-ой строки с максимальным значением
              var indexOfMaxNum = lineOfMatrix.ToList().IndexOf(maxNum); //Получаем индекс этого элемента
              if(matrix[i,indexOfMaxNum] < sumOfLine[i]-matrix[i,indexOfMaxNum])
              {
                Console.WriteLine("Matrix doesn't fit to this method");
                Fill(sumOfLine, 0);
                return sumOfLine;
              }
              for (var p = 0; p < m; p++)
              {
                var temping = matrix[i, p];
                matrix[i,p] = matrix[indexOfMaxNum,p];
                matrix[indexOfMaxNum,p] = temping;    
              } //Меняем строки местами так, чтобы максимальный элемент i-ой строки стал диагональным в матрице
                         
          }

          var matrixA = new double[n, n];
          for (var i = 0; i < n; i++)
            for (var j = 0; j < n; j++)
              matrixA[i, j] = matrix[i, j];

          var matrixB = new double[n];
          for (var i = 0; i < n; i++)
              matrixB[i]=matrix[i,n];
          
          var answer = new double[n];
          var temp = new double[n];
          Fill(answer,0); Fill(temp, 0);
          do
          {
              for (var i = 0; i < n; i++)
              {
                  answer[i] = matrixB[i]/matrix[i,i];
                  for (var j = 0; j < m - 1; j++)
                  {
                      if (i == j) continue;
                      answer[i] -= matrixA[i, j]/matrix[i,i] * temp[j];
                  }
              }
              for (var p = 0; p <n; p++)
                  if (Math.Abs(answer[p] - temp[p]) < e) return answer;
              
              for (var k = 0; k <n; k++)
                  temp[k] = answer[k];
          } while (true);
        }

        private static void Fill<T>(IList<T> array, T value)
        {
            for (var i = 0; i < array.Count; i++)
            {
                array[i] = value;
            }
        }

        public static void SolveSlau()
        {
            string matrixText;
            var matrixTxtPath = @Path.Combine(Directory.GetCurrentDirectory(),"matrix.txt");
            if (File.Exists(matrixTxtPath))
            {
                matrixText = File.ReadAllText(matrixTxtPath);
            }
            else
            {
                using (var fs = File.Create(matrixTxtPath))     
                {    
                    // Add some text to file    
                    var title = new UTF8Encoding(true).GetBytes(
                        "1 0 0 1 \n 1 0 1 1 \n 1 0 0 1");    
                    fs.Write(title, 0, title.Length);
                }    
                matrixText = File.ReadAllText(matrixTxtPath);
            }
            Console.WriteLine("If you want to change matrix, go to "+matrixTxtPath);
            var n = Regex.Matches(matrixText,"\n").Count+1;
            var matrix = new double[n, n+1];
            var line = 0;
            foreach (var row in matrixText.Split('\n'))
            {
                var column = 0;
                foreach (var col in row.Trim().Split(' '))
                {
                    matrix[line, column] = double.Parse(col.Trim());
                    column++;
                }
                line++;
            }
        
            for (var k = 0; k < n; k++)
            {
                for (var i = 0; i < (n + 1); i++)
                {
                    Console.Write(matrix[k,i]+" ");
                } Console.Write("\n");
            } //Создаём и печатаем новую матрицу


            Console.WriteLine("Enter method to solve this matrix \n 1. Method of Gauss \n 2. Method of Thomas \n 3.Method of Iteration \n 4.Exit");
            var method = Console.ReadLine();
            var answer = new double[n];
            switch (method)
            {
                case "1": answer = Algorithms.Maths.Gauss(matrix);break;
                case "2": answer = Algorithms.Maths.Thomas(matrix); break;
                case "3": Console.WriteLine("Enter accuracy"); var e = Convert.ToDouble(Console.ReadLine()); 
                    answer = Algorithms.Maths.Iteration(matrix, e); break;
                case "4": return;
                default: Console.WriteLine("You need to write a number from 1 to 3"); break;
            }
        
            for(var i=0;i<n;i++)
                Console.WriteLine("x"+(i+1)+" : "+answer[i]);

        }
        
        public static double F(double x)
        {
            return Math.Pow(x,3)-2*Math.Pow(x,2)-4*x+7;
        }

        public static double[,] FindRootRanges(double a, double b, double e)
        {
            var n = Convert.ToInt32(((b-a)/e)+1);
            var numbers = new double[n+1];
            var ranges = new double[n,2];
            for(var i=0;i<=n;i++)
                numbers[i] = a+e*(Convert.ToDouble(i)-1);
            int c=0;
            for(var i=1;i<=n;i++)
            {
                if(F(numbers[i-1])*F(numbers[i])<0)
                {
                    ranges[c,0]= numbers[i-1];
                    ranges[c,1]=numbers[i];
                    c++;
                }
            }
            return ranges;
        }
    }
}


internal abstract class Program
{
    public static void Main()
    {
      var rang = Algorithms.Maths.FindRootRanges(-10,10,0.0001);

     for(var i=0;i<rang.GetLength(0); i++)
     {
        for(var j=0; j<rang.GetLength(1);j++){
            if(rang[i,0]!=0 && rang[i,1]!=0)
                Console.Write(rang[i,j]+"\t");
        }
        if(rang[i,0]!=0)
           Console.Write("\n"); 
     }
      
    }
}